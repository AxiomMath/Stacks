module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StalkSectionsPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationStalkIdentifications

/-!
# The stalk of an abelian étale sheaf is its sections over the strict henselization

Let `S` be a scheme, `s` a geometric point of `S` and `p : Spec(𝒪^{sh}_{S,s}) ⟶ S` the structure
morphism of the strict henselization at `s`. For an abelian sheaf `F` on the small étale site of
`S` the canonical map

`F_s ⟶ Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)`

of Tag 0GJN, which carries the germ at `s` of a section over an étale neighbourhood `W` to its
restriction along the canonical morphism `Spec(𝒪^{sh}_{S,s}) ⟶ W`, is an isomorphism. This is
the degree-zero content of [Stacks, Tag 03Q9], and it needs no hypothesis on `S`.

## Main results

* `AlgebraicGeometry.isIso_etaleStalkToSectionsAb_id` (in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationStalkIdentifications`) —
  **[Stacks, Tag 03Q9] in degree zero**: the map `F_s ⟶ Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)` is an
  isomorphism, naturally in `F`.
* `AlgebraicGeometry.etaleStalkSectionsAbIso` — that isomorphism.

## The route

The strict henselization is the spectrum of the étale local ring, which is strictly henselian
local (`AlgebraicGeometry.etaleLocalRing_strictHenselian`), and the canonical geometric point
`ι : Spec κ(s) ⟶ Spec(𝒪^{sh}_{S,s})` hits its closed point
(`AlgebraicGeometry.geometricPointToStrictHenselization_closedPoint`). Over such a base the
étale neighbourhoods of such a point have an initial object, the identity neighbourhood
(`Stacks.EtaleCohomology.isInitialPointSmallEtaleClosedPointElement`), so global sections on the
strict henselization are the stalk at `ι`:

`Γ(Spec(𝒪^{sh}_{S,s}), G) = G_ι`,

which is `Stacks.EtaleCohomology.sheafFiberClosedPointIsoGamma'` with abelian coefficients. The
stalk of an inverse image is the stalk at the image point, which is Tag 03Q1 for abelian sheaves
(`Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso`), and `ι ≫ p = s` by Tag 0993. Composing,

`Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F) = (p⁻¹F)_ι = F_s`,

and what remains is that this composite is a right inverse of the map of Tag 0GJN; being one, it
is its inverse, that composite being invertible. Both composites out of the stalk at `s` are
compared on germs, where the first is restriction of a section along `Spec(𝒪^{sh}_{S,s}) ⟶ W`
followed by the germ at the initial neighbourhood, and the second is the unit of the
inverse-image adjunction followed by the germ at the corresponding lift of `ι` to the base change
`W ×_S Spec(𝒪^{sh}_{S,s})`. Those two lifts agree because a morphism into a fibre product is
determined by its two projections, which here are the chosen lift of `s` in `W` and `ι` itself.

## Implementation notes

The identification `ι ≫ p = s` is an equality of morphisms rather than a definitional one, so
the stalk functor at `ι ≫ p` and the stalk functor at `s` are transported into one another by
`Stacks.EtaleCohomology.smallEtaleStalkAbCongr`. All use of that transport is confined to
`Stacks.EtaleCohomology.toPresheafFiber_comp_smallEtaleStalkAbCongr_hom`, which compares the two
germ maps and is proved by substituting the equality; every other statement here is
transport-free. For the same reason the comparison of Tag 03Q1 on germs is restated as
`Stacks.EtaleCohomology.toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv_of_proj`, with the
lift to the base change given by its two projections instead of through the correspondence of
fibres.

The goals of the germ computation mention objects of a small étale site, which the elaborator
cannot see as type-correct under the `implicit` transparency level: the morphism property of
étale morphisms needs eta-expansion before it is one. That stops `rw` from firing on such a
goal, so the reassociations are stated for abstract morphisms in an abstract category and
applied by `exact`; this is the same device as in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/LocalAcyclicity/StalkSectionsPullback.lean`.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 0993](https://stacks.math.columbia.edu/tag/0993)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u u' v'

namespace Stacks.EtaleCohomology

/-! ### Two reassociations -/

section Bookkeeping

variable {C : Type*} [Category C]

/-- The reassociation behind
`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_sheafFiberClosedPointIsoGamma_inv`: a
composite of four maps whose first factors through a third object and whose middle two cancel. -/
private theorem comp_cancel_inv {A₀ A₁ A₂ A₃ A₄ : C} {b : A₀ ⟶ A₄} {c : A₄ ⟶ A₁} {i : A₁ ⟶ A₂}
    {j : A₂ ⟶ A₁} {t : A₁ ⟶ A₃} {a : A₀ ⟶ A₁} {d : A₄ ⟶ A₃} (ha : b ≫ c = a)
    (hij : i ≫ j = 𝟙 A₁) (hd : c ≫ t = d) :
    (a ≫ i) ≫ j ≫ t = b ≫ d := by
  subst ha hd
  rw [Category.assoc, ← Category.assoc i j t, hij, Category.id_comp, Category.assoc]

/-- The reassociation behind `AlgebraicGeometry.isIso_etaleStalkToSectionsAb_id`: a composite of
five maps, rewritten twice and with a cancelling pair in the middle, is its first factor. -/
private theorem germ_shuffle {A₀ A₁ A₂ A₃ A₄ A₅ : C} {T : A₀ ⟶ A₁} {a : A₁ ⟶ A₂} {e : A₂ ⟶ A₃}
    {h : A₃ ⟶ A₄} {q : A₄ ⟶ A₁} {c : A₀ ⟶ A₂} {b : A₀ ⟶ A₅} {d : A₅ ⟶ A₃} {T₀ : A₀ ⟶ A₄}
    {k : A₄ ⟶ A₃} (f₁ : T ≫ a = c) (f₂ : c ≫ e = b ≫ d) (f₃ : T₀ ≫ k = b ≫ d)
    (f₄ : k ≫ h = 𝟙 A₄) (f₅ : T₀ ≫ q = T) :
    T ≫ a ≫ e ≫ h ≫ q = T ≫ 𝟙 A₁ := by
  rw [Category.comp_id, reassoc_of% f₁, reassoc_of% f₂, ← reassoc_of% f₃, reassoc_of% f₄, f₅]

end Bookkeeping

/-! ### Germs at two names for the same geometric point -/

section Germs

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The stalk of an abelian étale sheaf at a geometric point depends on the point only through
the underlying morphism: two equal morphisms have the same stalk functor. -/
def smallEtaleStalkAbCongr {z z' : Spec (.of Ω) ⟶ X} (hz : z = z') :
    smallEtaleStalkAb z ≅ smallEtaleStalkAb z' :=
  eqToIso (congrArg (fun w : Spec (.of Ω) ⟶ X => smallEtaleStalkAb w) hz)

/-- The germ map at a geometric point depends on the point only through the underlying morphism:
for two equal morphisms the germ maps at corresponding lifts agree, modulo the transport of the
stalk along that equality. -/
theorem toPresheafFiber_comp_smallEtaleStalkAbCongr_hom {z z' : Spec (.of Ω) ⟶ X} (hz : z = z')
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale z).fiber.obj W)
    (v' : (Scheme.pointSmallEtale z').fiber.obj W) (hv : v.left = v'.left) :
    (Scheme.pointSmallEtale z).toPresheafFiber W v F.obj ≫
        (smallEtaleStalkAbCongr hz).hom.app F =
      (Scheme.pointSmallEtale z').toPresheafFiber W v' F.obj := by
  subst hz
  obtain rfl : v = v' := CategoryTheory.Over.OverMorphism.ext hv
  exact Category.comp_id _

variable {X' : Scheme.{u}} (g : X' ⟶ X) (y : Spec (.of Ω) ⟶ X')

/-- **Tag 03Q1 for abelian sheaves, on germs, with the lift to the base change named by its two
projections.** On the germ at `y ≫ g` of a section over an étale neighbourhood `W`, the
comparison of stalks is the unit of the inverse-image/direct-image adjunction followed by the
germ at any lift of `y` to `W ×_X X'` whose projection to `W` is the chosen lift of `y ≫ g` and
whose projection to `X'` is `y`.

Those two projections determine the lift, so this is
`Stacks.EtaleCohomology.toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv` with the
correspondence of fibres eliminated. -/
theorem toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv_of_proj
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale (y ≫ g)).fiber.obj W)
    (u : (Scheme.pointSmallEtale y).fiber.obj ((smallEtaleBaseChange g).obj W))
    (hu₁ : u.left ≫ pullback.fst W.hom g = v.left)
    (hu₂ : u.left ≫ pullback.snd W.hom g = y) :
    (Scheme.pointSmallEtale (y ≫ g)).toPresheafFiber W v F.obj ≫
        (smallEtaleStalkPullbackAbIso g y).inv.app F =
      ((smallEtaleAdjunctionAb g).unit.app F).hom.app (op W) ≫
        (Scheme.pointSmallEtale y).toPresheafFiber ((smallEtaleBaseChange g).obj W) u
          ((smallEtalePullbackAb g).obj F).obj := by
  obtain rfl : u = (pointSmallEtaleComapFiberIso g y).hom.app W v :=
    Over.OverMorphism.ext (pullback.hom_ext
      (hu₁.trans (pointSmallEtaleComapFiberIso_hom_app_left_fst g y W v).symm)
      (hu₂.trans (pointSmallEtaleComapFiberIso_hom_app_left_snd g y W v).symm))
  exact toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv g y F W v

end Germs

/-! ### Sections on a strictly henselian local base, on germs -/

section ClosedPoint

variable {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω]
  [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of R))
  (hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint R)

/-- The germ at the geometric point of a section over the final object of the small étale site
of `Spec R`, as a natural transformation in the presheaf, with coefficients in an arbitrary
category. This generalizes `Stacks.EtaleCohomology.sectionsToPresheafFiberClosedPoint`, which is
stated for presheaves of sets. -/
def sectionsToPresheafFiberClosedPoint' (A : Type u') [Category.{v'} A]
    [HasColimitsOfSize.{u, u} A] :
    (evaluation (Spec (.of R)).Etaleᵒᵖ A).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of R))))) ⟶
      (pointSmallEtale x).presheafFiber :=
  (pointSmallEtale x).toPresheafFiberNatTrans
    (Scheme.Etale.mk (𝟙 (Spec (.of R)))) (pointSmallEtaleClosedPointElement x)

/-- **Over a strictly henselian local ring the fibre at a geometric point above the closed point
is evaluation at the final object**, for presheaves with values in an arbitrary category: the
étale neighbourhoods of that point have an initial object, so the colimit computing the fibre is
attained there. This generalizes `Stacks.EtaleCohomology.presheafFiberClosedPointIsoSections`,
which is stated for presheaves of sets. -/
def presheafFiberClosedPointIsoSections' (A : Type u') [Category.{v'} A]
    [HasColimitsOfSize.{u, u} A] :
    (evaluation (Spec (.of R)).Etaleᵒᵖ A).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of R))))) ≅
      (pointSmallEtale x).presheafFiber := by
  let : ∀ P, IsIso ((sectionsToPresheafFiberClosedPoint' x A).app P) := fun P ↦
    ((pointSmallEtale x).isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal
      (op ⟨Scheme.Etale.mk (𝟙 (Spec (.of R))), pointSmallEtaleClosedPointElement x⟩)
      (isInitialPointSmallEtaleClosedPointElement x hx).op
  let := NatIso.isIso_of_isIso_app (sectionsToPresheafFiberClosedPoint' x A)
  exact asIso (sectionsToPresheafFiberClosedPoint' x A)

/-- **Over a strictly henselian local ring the stalk of a sheaf at a geometric point above the
closed point is its object of global sections.** Both are evaluation at the final object of the
small étale site, the stalk because the point lifts to that object initially. The coefficient
category is arbitrary; this generalizes `Stacks.EtaleCohomology.sheafFiberClosedPointIsoGamma`,
which is stated for sheaves of sets. -/
@[sga "4 VIII 4.6" "more general", sga "4 VIII 7.7" "special case"]
def sheafFiberClosedPointIsoGamma' (A : Type u') [Category.{v'} A]
    [HasColimitsOfSize.{u, u} A]
    [HasWeakSheafify (smallEtaleTopology (Spec (.of R))) A] :
    (pointSmallEtale x).sheafFiber (A := A) ≅
      Sheaf.Γ (smallEtaleTopology (Spec (.of R))) A :=
  (Functor.isoWhiskerLeft
      (sheafToPresheaf (smallEtaleTopology (Spec (.of R))) A)
      (presheafFiberClosedPointIsoSections' x hx A)).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R))) A
      (isTerminalEtaleMkId (Spec (.of R)))).symm

/-- The identification of global sections with the stalk at a geometric point above the closed
point is, in the direction from sections, the germ at the identity neighbourhood. -/
theorem sheafFiberClosedPointIsoGamma_inv_app
    (G : Sheaf (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}) :
    (sheafFiberClosedPointIsoGamma' x hx Ab.{u + 1}).inv.app G =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}
          (isTerminalEtaleMkId (Spec (.of R)))).hom.app G ≫
        (Scheme.pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 (Spec (.of R))))
          (pointSmallEtaleClosedPointElement x) G.obj :=
  rfl

/-- **Restriction of sections, read as a germ at the closed point.** Over a strictly henselian
local base, restricting a section over an étale neighbourhood `W` of the base to a global section
of the inverse image and then taking its germ at a geometric point above the closed point is the
unit of the inverse-image adjunction followed by the germ at the lift of that point to the base
change of `W`. -/
theorem smallEtaleSectionsPullbackAb_comp_sheafFiberClosedPointIsoGamma_inv
    {Z : Scheme.{u}} (g : Spec (.of R) ⟶ Z) (W : Z.Etale) (r : Spec (.of R) ⟶ W.left)
    (hr : r ≫ W.hom = g) (F : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtaleSectionsPullbackAb g W r hr).app F ≫
        (sheafFiberClosedPointIsoGamma' x hx Ab.{u + 1}).inv.app
          ((smallEtalePullbackAb g).obj F) =
      ((smallEtaleAdjunctionAb g).unit.app F).hom.app (op W) ≫
        (Scheme.pointSmallEtale x).toPresheafFiber ((smallEtaleBaseChange g).obj W)
          ((Scheme.pointSmallEtale x).fiber.map (smallEtaleBaseChangeLift g W r hr)
            (pointSmallEtaleClosedPointElement x))
          ((smallEtalePullbackAb g).obj F).obj :=
  (congrArg (fun z => (smallEtaleSectionsPullbackAb g W r hr).app F ≫ z)
      (sheafFiberClosedPointIsoGamma_inv_app x hx ((smallEtalePullbackAb g).obj F))).trans
    (comp_cancel_inv
      (Stacks.Sites.sectionsPullbackComparison_app (smallEtaleBaseChange g) Ab.{u + 1}
        (smallEtaleTopology Z) (smallEtaleTopology (Spec (.of R))) (smallEtaleAdjunctionAb g)
        (smallEtaleBaseChangeLift g W r hr) F).symm
      ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}
          (isTerminalEtaleMkId (Spec (.of R)))).inv_hom_id_app
        ((smallEtalePullbackAb g).obj F))
      (GrothendieckTopology.Point.toPresheafFiber_w (Scheme.pointSmallEtale x)
        (smallEtaleBaseChangeLift g W r hr) (pointSmallEtaleClosedPointElement x)
        ((smallEtalePullbackAb g).obj F).obj))

end ClosedPoint

end Stacks.EtaleCohomology

end
