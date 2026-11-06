module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationComponentLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreEtaleSectionsHenselianLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedBaseFieldSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections over a geometric fibre, and Stacks 0A3T over a strictly henselian local base

Let `f : X ⟶ S` be a morphism of schemes and `x : Spec Ω ⟶ S` a geometric point, `Ω` a
separably closed field. The fibre of `f` at `x` is `X_x = X ×_S Spec Ω`, and a sheaf of sets `F`
on `X_étale` restricts to `F_x = p⁻¹F` on `(X_x)_étale`, where `p : X_x ⟶ X`. The comparison
of the stalk `(f_*F)_x` with `Γ(X_x, F_x)` is the base change map `x⁻¹f_*F ⟶ q_*p⁻¹F` of the
cartesian square read on global sections over `Spec Ω`, and this file supplies the two
identifications that turn that map into one between the stalk and the sections over the fibre.

Over the spectrum of a separably closed field the étale neighbourhoods of the canonical point
have an initial object, namely the final object of the site with its identity lift, so the
stalk at that point is evaluation there, which is global sections. Separately, base change
along any morphism carries a final object of the small étale site to a final object, so the
global sections of a direct image are the global sections of the sheaf itself.

The same initiality holds over the spectrum of a strictly henselian local ring `R`, for a
geometric point above the closed point: an étale `Spec R`-scheme with a lift of that point has a
section through the lift, and only one. So over such a base the stalk of a direct image is the
set of global sections upstairs, and the chain of Tag 0A3T can be run: restriction to the closed
fibre by [Stacks, Tag 0A3S], then extension of the separably closed residue field to `Ω` by
[Stacks, Tag 0A3I].

## Main definitions

* `Stacks.EtaleCohomology.pointSmallEtaleIdElement` and
  `Stacks.EtaleCohomology.isInitialPointSmallEtaleIdElement` — the identity lift of the
  canonical point of the spectrum of a separably closed field, and its initiality among the
  étale neighbourhoods of that point.
* `Stacks.EtaleCohomology.pointSmallEtaleClosedPointElement` and
  `Stacks.EtaleCohomology.isInitialPointSmallEtaleClosedPointElement` — the same over the
  spectrum of a strictly henselian local ring, for a geometric point above the closed point.
* `Stacks.EtaleCohomology.smallEtaleInverseImageComp` — inverse image along `f` after inverse
  image along `g` is inverse image along `f ≫ g`, for sheaves of sets.

## Main results

* `Stacks.EtaleCohomology.presheafFiberIdIsoSections` and
  `Stacks.EtaleCohomology.sheafFiberIdIsoGamma` — the fibre, respectively the stalk of a sheaf
  of sets, at the canonical point of the spectrum of a separably closed field is evaluation at
  the final object, that is global sections.
* `Stacks.EtaleCohomology.smallEtalePushforwardGammaIso` — global sections of a direct image of
  sheaves of sets are the global sections of the sheaf itself.
* `Stacks.EtaleCohomology.isOpenImmersion_of_etale_section` and
  `Stacks.EtaleCohomology.eq_of_etale_section_of_comp_eq` — a section of an étale morphism is an
  open immersion, and over a local ring two sections agreeing on a point of the closed fibre are
  equal.
* `Stacks.EtaleCohomology.presheafFiberClosedPointIsoSections` and
  `Stacks.EtaleCohomology.sheafFiberClosedPointIsoGamma` — over a strictly henselian local ring
  the fibre, respectively the stalk, at a geometric point above the closed point is global
  sections.
* `Stacks.EtaleCohomology.pushforwardSheafFiberClosedPointIsoGamma` — **[Stacks, Tag 03Q9] for
  sheaves of sets in degree zero, over a strictly henselian local base**: the stalk of `f_*F` at
  such a point is `Γ(X, F)`. No hypothesis is carried.
* `Stacks.EtaleCohomology.pushforwardSheafFiberClosedPointIsoClosedFibreGamma` and
  `Stacks.EtaleCohomology.pushforwardSheafFiberClosedPointIsoGeometricFibreGamma` — for `f`
  proper over a strictly henselian local base, the stalk of `f_*F` at such a point is the set of
  global sections over the closed fibre, respectively over the geometric fibre. Both carry the
  hypothesis `hcompat` of [Stacks, Tag 0A3S].
* `Stacks.EtaleCohomology.closedFibreBaseChange_fst_comp_closedFibreInclusion` — the scheme
  whose sections the previous isomorphism computes is the geometric fibre:
  `(X ×_{Spec R} Spec κ(R)) ×_{Spec κ(R)} Spec Ω` projects to `X` as `X ×_{Spec R} Spec Ω` does.
* `Stacks.EtaleCohomology.properGeometricFibreComparison` — the comparison map of Tag 0A3T for
  an arbitrary base, and `isIso_properGeometricFibreComparison_of_isIso`, its bijectivity
  granted that the base change map of the cartesian square is an isomorphism.

## Implementation notes

**No tag attribute for Tag 0A3T is attached, and its bijectivity over an arbitrary base is not
asserted.** The proof of the tag is the composite of Tag 03Q9 for sheaves of sets, which
identifies `(f_*F)_x` with the sections of `p⁻¹F` over `X ×_S Spec(O^{sh}_{S,x})`, with
Tag 0A3S for the proper morphism `X ×_S Spec(O^{sh}_{S,x}) ⟶ Spec(O^{sh}_{S,x})` over the
strictly henselian local base, and with Tag 0A3I for the extension of the separably closed
residue field of that base to `Ω`. All three are run here, in
`pushforwardSheafFiberClosedPointIsoGeometricFibreGamma`, *for a base that is already the
spectrum of a strictly henselian local ring*: there Tag 03Q9 is the initiality above and needs
nothing, Tag 0A3S is
`isIso_globalSectionsComparison_closedFibre_of_henselianLocalRing` and contributes its
hypothesis `hcompat`, and Tag 0A3I is
`globalSectionsSmallEtaleInverseImageIso_of_isSepClosed`.

Two inputs are therefore still owed for an arbitrary base.

The first is Tag 03Q9 itself, for sheaves of sets: the reduction of an arbitrary base `S` to
`Spec(O^{sh}_{S,x})`, which is what the restricted form proved here does *not* supply — over a
strictly henselian local base the strict henselization is the base and the reduction is vacuous.
In the source it rests on Tag 03Q6, that étale cohomology commutes with the limit of the affine
étale neighbourhoods of the point, and through it on Tag 09YQ; neither is formalized. The
geometry of that limit is available, as
`AlgebraicGeometry.strictHenselizationConeIsLimit`, but the statement about sections is not.

The second is the surjectivity half of Tag 09ZF, which Tag 0A3S consumes and which rests on
Tag 09Z0 and Tag 09Z3; it is carried as `hcompat`, asking that every global section of
`F|_{X₀}` admit a presenting family of sections of `F` over objects of the small étale site
covering `X` which agree on the pairwise fibre products.

The comparison map of the tag over an arbitrary base is `properGeometricFibreComparison`, and
`isIso_properGeometricFibreComparison_of_isIso` reduces its bijectivity to the base change map
`Stacks.EtaleCohomology.smallEtaleSetBaseChange` of the cartesian square defining `X_x` being an
isomorphism, which is the assertion of Tag 0A3U at a geometric point.

## References

* [Stacks Project, Tag 0A3T](https://stacks.math.columbia.edu/tag/0A3T)
* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
* [Stacks Project, Tag 0A3I](https://stacks.math.columbia.edu/tag/0A3I)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology


section SepClosedPoint

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- The identity, viewed as a lift of the canonical point of `Spec Ω` to the final object of the
small étale site of `Spec Ω`. -/
def pointSmallEtaleIdElement :
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) :=
  CategoryTheory.Over.homMk (𝟙 _) (by
    change (𝟙 (Spec (.of Ω))) ≫ (𝟙 (Spec (.of Ω))) = 𝟙 (Spec (.of Ω))
    simp)

/-- The final object of the small étale site of `Spec Ω` with its identity lift is an initial
étale neighbourhood of the canonical point: a lift of the canonical point to an étale
`Spec Ω`-scheme is itself the unique morphism of neighbourhoods out of this one. -/
def isInitialPointSmallEtaleIdElement :
    IsInitial (show (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.Elements from
      (Functor.Elements.mk (obj := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) (pointSmallEtaleIdElement Ω))) := by
  apply IsInitial.ofUniqueHom
    (fun U : (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.Elements ↦
      Functor.Elements.homMk
      (MorphismProperty.Over.homMk U.val.left (CategoryTheory.Over.w U.val)) ?_)
    (fun U morphism ↦ ?_)
  · apply CategoryTheory.Over.OverMorphism.ext
    change (𝟙 (Spec (.of Ω))) ≫ U.val.left = U.val.left
    exact Category.id_comp _
  · apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    have h : 𝟙 (Spec (.of Ω)) ≫ morphism.hom.left = U.val.left :=
      congrArg (fun b ↦ b.left) morphism.map_val
    exact (Category.id_comp morphism.1.left).symm.trans h

/-- The germ at the canonical point of `Spec Ω` of a section over the final object of the small
étale site, as a natural transformation in the presheaf. -/
def sectionsToPresheafFiberId :
    (evaluation (Spec (.of Ω)).Etaleᵒᵖ (Type (max (u + 1) v))).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ⟶
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).presheafFiber :=
  (pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiberNatTrans
    (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) (pointSmallEtaleIdElement Ω)

/-- **The fibre at the canonical point of the spectrum of a separably closed field is evaluation
at the final object.** The étale neighbourhoods of that point have an initial object, so the
colimit computing the fibre of a presheaf is attained there. -/
def presheafFiberIdIsoSections :
    (evaluation (Spec (.of Ω)).Etaleᵒᵖ (Type (max (u + 1) v))).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ≅
      (pointSmallEtale (𝟙 (Spec (.of Ω)))).presheafFiber := by
  letI : ∀ P, IsIso ((sectionsToPresheafFiberId.{u, v} Ω).app P) := fun P ↦
    ((pointSmallEtale (𝟙 (Spec (.of Ω)))).isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal
      (op (Functor.Elements.mk (obj := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) (pointSmallEtaleIdElement Ω)))
      (isInitialPointSmallEtaleIdElement Ω).op
  letI := NatIso.isIso_of_isIso_app (sectionsToPresheafFiberId.{u, v} Ω)
  exact asIso (sectionsToPresheafFiberId.{u, v} Ω)

/-- **The stalk of a sheaf of sets at the canonical point of the spectrum of a separably closed
field is its set of global sections.** Both are evaluation at the final object of the small
étale site, the stalk because the identity lift is an initial étale neighbourhood. -/
def sheafFiberIdIsoGamma :
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber (A := Type (max (u + 1) v)) ≅
      Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (Type (max (u + 1) v)) :=
  (Functor.isoWhiskerLeft
      (sheafToPresheaf (smallEtaleTopology (Spec (.of Ω))) (Type (max (u + 1) v)))
      (presheafFiberIdIsoSections.{u, v} Ω)).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of Ω))) (Type (max (u + 1) v))
      (isTerminalEtaleMkId (Spec (.of Ω)))).symm

end SepClosedPoint

/-- **Global sections of a direct image are the global sections of the sheaf.** Base change
along `g` carries the final object of the small étale site of `S` to a final object of the small
étale site of `T`, and sections of `g_*G` over the former are sections of `G` over the latter. -/
def smallEtalePushforwardGammaIso {T S : Scheme.{u}} (g : T ⟶ S) :
    (smallEtaleBaseChange g).sheafPushforwardContinuous (Type (max (u + 1) v))
          (smallEtaleTopology S) (smallEtaleTopology T) ⋙
        Sheaf.Γ (smallEtaleTopology S) (Type (max (u + 1) v)) ≅
      Sheaf.Γ (smallEtaleTopology T) (Type (max (u + 1) v)) :=
  Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology S) (Type (max (u + 1) v))
        (isTerminalEtaleMkId S)) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) ≪≫
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (max (u + 1) v))
      (isTerminalSmallEtaleBaseChangeObj g (isTerminalEtaleMkId S))).symm

section Stalk

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)

/-- The canonical point of `Spec Ω` composed with `x` is `x`, so the two stalk functors agree. -/
def pointSmallEtaleIdCompIso :
    (pointSmallEtale (𝟙 (Spec (.of Ω)) ≫ x)).sheafFiber (A := Type (max (u + 1) v)) ≅
      (pointSmallEtale x).sheafFiber :=
  eqToIso (congrArg (fun y : Spec (.of Ω) ⟶ S ↦
    (pointSmallEtale y).sheafFiber (A := Type (max (u + 1) v))) (Category.id_comp x))

/-- **The stalk at a geometric point is the global sections of the inverse image.** The stalk of
the inverse image along `x` at the canonical point of `Spec Ω` is the stalk at `x`, and over the
spectrum of a separably closed field the stalk at the canonical point is global sections. -/
def stalkIsoInverseImageGamma :
    (pointSmallEtale x).sheafFiber (A := Type (max (u + 1) v)) ≅
      smallEtaleInverseImage.{u, v} x ⋙
        Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (Type (max (u + 1) v)) :=
  (pointSmallEtaleIdCompIso.{u, v} x).symm ≪≫
    (smallEtaleInverseImageStalkIso.{v, u} x (𝟙 (Spec (.of Ω)))).symm ≪≫
    Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, v} x) (sheafFiberIdIsoGamma.{u, v} Ω)

end Stalk

section GeometricFibre

variable {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (.of Ω) ⟶ S)

/-- **The comparison map of Stacks Project, Tag 0A3T.** For a morphism `f : X ⟶ S` and a
geometric point `x : Spec Ω ⟶ S`, the canonical map from the stalk `(f_*F)_x` to the global
sections of `F_x = p⁻¹F` on the fibre `X_x = X ×_S Spec Ω`, naturally in the sheaf of sets `F`:
the base change map of the cartesian square, read on global sections over `Spec Ω` through the
identification of the stalk at `x` with the global sections of the inverse image and of the
global sections of a direct image with the global sections upstairs.

Tag 0A3T asserts that this map is bijective when `f` is proper. That is not proved here; see the
implementation notes. -/
@[sga "4 XII 5.2"]
def properGeometricFibreComparison :
    (smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
          (smallEtaleTopology S) (smallEtaleTopology X) ⋙
        (pointSmallEtale x).sheafFiber ⟶
      smallEtaleInverseImage.{u, v} (pullback.fst f x) ⋙
        Sheaf.Γ (smallEtaleTopology (pullback f x)) (Type (max (u + 1) v)) :=
  (Functor.isoWhiskerLeft _ (stalkIsoInverseImageGamma.{u, v} x)).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (smallEtaleSetBaseChange.{u, v} (pullback.fst f x) (pullback.snd f x) f x
        pullback.condition)
      (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (Type (max (u + 1) v))) ≫
    (Functor.associator _ _ _).hom ≫
    (Functor.isoWhiskerLeft _
      (smallEtalePushforwardGammaIso.{u, v} (pullback.snd f x))).hom

/-- The comparison of Tag 0A3T is an isomorphism as soon as the base change map of the cartesian
square defining the geometric fibre is one: the three remaining factors of the comparison are
isomorphisms by construction.

This is the precise reduction of Tag 0A3T to the assertion of Tag 0A3U at a geometric point. -/
theorem isIso_properGeometricFibreComparison_of_isIso
    (h : IsIso (smallEtaleSetBaseChange.{u, v} (pullback.fst f x) (pullback.snd f x) f x
      pullback.condition)) :
    IsIso (properGeometricFibreComparison.{u, v} f x) := by
  dsimp only [properGeometricFibreComparison]
  infer_instance

end GeometricFibre

section StrictlyHenselianBase

/-- A section of an étale morphism is an open immersion: being split it is a monomorphism, and
a flat monomorphism of schemes is an open immersion. -/
@[ega "IV 16.2.3" "special case", ega "IV 17.9.3", sga "6 VIII 1.3" "more general"]
theorem isOpenImmersion_of_etale_section {T S : Scheme.{u}} (g : T ⟶ S) [Etale g] (t : S ⟶ T)
    (ht : t ≫ g = 𝟙 S) : IsOpenImmersion t := by
  have : Etale (t ≫ g) := ht ▸ inferInstance
  have : Etale t := Etale.of_comp t g
  have : IsSplitMono t := IsSplitMono.mk' ⟨g, ht⟩
  exact IsOpenImmersion.of_flat_of_mono t

variable {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R]

/-- **Two sections of an étale morphism to the spectrum of a local ring which agree on a point
of the closed fibre are equal.** Each section is an open immersion, so the locus where one
factors through the other is open; it contains the closed point, hence is everything, and the
factoring morphism is then a section of the identity. -/
theorem eq_of_etale_section_of_comp_eq {T : Scheme.{u}} (g : T ⟶ Spec (.of R)) [Etale g]
    {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ Spec (.of R))
    (hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint R)
    (t t' : Spec (.of R) ⟶ T) (ht : t ≫ g = 𝟙 _) (ht' : t' ≫ g = 𝟙 _)
    (hcomp : x ≫ t = x ≫ t') : t = t' := by
  have hpt : t (IsLocalRing.closedPoint R) = t' (IsLocalRing.closedPoint R) := by
    simpa only [Scheme.Hom.comp_apply, hx] using
      congrArg (fun k : Spec (.of Ω) ⟶ T ↦ k (default : Spec (.of Ω))) hcomp
  have hoi : IsOpenImmersion t' := isOpenImmersion_of_etale_section g t' ht'
  have hclosed : IsLocalRing.closedPoint R ∈ t ⁻¹ᵁ t'.opensRange := by
    show t (IsLocalRing.closedPoint R) ∈ t'.opensRange
    rw [Scheme.Hom.mem_opensRange]
    exact ⟨IsLocalRing.closedPoint R, hpt.symm⟩
  have htop : t ⁻¹ᵁ t'.opensRange = ⊤ := IsLocalRing.closed_point_mem_iff.mp hclosed
  have hrange : Set.range t ⊆ Set.range t' := by
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ t ⁻¹ᵁ t'.opensRange := by rw [htop]; trivial
    exact Scheme.Hom.mem_opensRange.mp hz
  have hl : IsOpenImmersion.lift t' t hrange ≫ t' = t := IsOpenImmersion.lift_fac t' t hrange
  have hid : IsOpenImmersion.lift t' t hrange = 𝟙 _ := by
    have h : IsOpenImmersion.lift t' t hrange ≫ t' ≫ g = t ≫ g := by
      rw [← Category.assoc, hl]
    rwa [ht', Category.comp_id, ht] at h
  rw [← hl, hid, Category.id_comp]

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of R))
  (hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint R)

/-- The final object of the small étale site of `Spec R`, with the geometric point itself as its
lift, viewed as an étale neighbourhood of that point. -/
def pointSmallEtaleClosedPointElement :
    (pointSmallEtale x).fiber.obj (Scheme.Etale.mk (𝟙 (Spec (.of R)))) :=
  CategoryTheory.Over.homMk x (by
    change x ≫ (𝟙 (Spec (.of R))) = x
    simp)

/-- **Over a strictly henselian local ring the étale neighbourhoods of a geometric point above
the closed point have an initial object**, namely the final object of the small étale site with
the point itself as its lift: an étale scheme with a lift of the point admits a section through
that lift, and only one. -/
@[ega "IV 18.5.11" "special case", sga "3 X 4.5" "special case"]
def isInitialPointSmallEtaleClosedPointElement :
    IsInitial (show (pointSmallEtale x).fiber.Elements from
      (Functor.Elements.mk (obj := Scheme.Etale.mk (𝟙 (Spec (.of R)))) (pointSmallEtaleClosedPointElement x))) := by
  classical
  have hsec : ∀ U : (pointSmallEtale x).fiber.Elements,
      ∃ t : Spec (.of R) ⟶ U.obj.left,
        t ≫ U.obj.hom = 𝟙 (Spec (.of R)) ∧ x ≫ t = U.val.left := fun U ↦ by
    let : Etale U.obj.hom := U.obj.prop
    exact AlgebraicGeometry.exists_hom_of_strictlyHenselian
      ({ residueField := Ω, hom := x } : GeometricPoint (Spec (.of R)))
      (𝟙 (Spec (.of R))) x (Category.comp_id x) hx U.obj.hom U.val.left
      (CategoryTheory.Over.w U.val)
  refine IsInitial.ofUniqueHom (fun U ↦ Functor.Elements.homMk
    (MorphismProperty.Over.homMk (hsec U).choose (hsec U).choose_spec.1) ?_) (fun U m ↦ ?_)
  · apply CategoryTheory.Over.OverMorphism.ext
    change x ≫ (hsec U).choose = U.val.left
    exact (hsec U).choose_spec.2
  · apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    let : Etale U.obj.hom := U.obj.prop
    have hw : m.hom.left ≫ U.obj.hom = 𝟙 (Spec (.of R)) := CategoryTheory.Over.w m.hom.hom
    have hpoint : x ≫ m.hom.left = U.val.left := congrArg (fun b ↦ b.left) m.map_val
    exact eq_of_etale_section_of_comp_eq U.obj.hom x hx m.hom.left (hsec U).choose hw
      (hsec U).choose_spec.1 (hpoint.trans (hsec U).choose_spec.2.symm)

/-- The germ at the geometric point of a section over the final object of the small étale site
of `Spec R`, as a natural transformation in the presheaf. -/
def sectionsToPresheafFiberClosedPoint :
    (evaluation (Spec (.of R)).Etaleᵒᵖ (Type (max (u + 1) v))).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of R))))) ⟶
      (pointSmallEtale x).presheafFiber :=
  (pointSmallEtale x).toPresheafFiberNatTrans
    (Scheme.Etale.mk (𝟙 (Spec (.of R)))) (pointSmallEtaleClosedPointElement x)

/-- **Over a strictly henselian local ring the fibre at a geometric point above the closed point
is evaluation at the final object**, for presheaves: the étale neighbourhoods of that point have
an initial object, so the colimit computing the fibre is attained there. -/
def presheafFiberClosedPointIsoSections :
    (evaluation (Spec (.of R)).Etaleᵒᵖ (Type (max (u + 1) v))).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of R))))) ≅
      (pointSmallEtale x).presheafFiber := by
  letI : ∀ P, IsIso ((sectionsToPresheafFiberClosedPoint.{u, v} x).app P) := fun P ↦
    ((pointSmallEtale x).isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal
      (op (Functor.Elements.mk (obj := Scheme.Etale.mk (𝟙 (Spec (.of R)))) (pointSmallEtaleClosedPointElement x)))
      (isInitialPointSmallEtaleClosedPointElement x hx).op
  letI := NatIso.isIso_of_isIso_app (sectionsToPresheafFiberClosedPoint.{u, v} x)
  exact asIso (sectionsToPresheafFiberClosedPoint.{u, v} x)

/-- **Over a strictly henselian local ring the stalk of a sheaf of sets at a geometric point
above the closed point is its set of global sections.** Both are evaluation at the final object
of the small étale site, the stalk because the point lifts to that object initially. -/
def sheafFiberClosedPointIsoGamma :
    (pointSmallEtale x).sheafFiber (A := Type (max (u + 1) v)) ≅
      Sheaf.Γ (smallEtaleTopology (Spec (.of R))) (Type (max (u + 1) v)) :=
  (Functor.isoWhiskerLeft
      (sheafToPresheaf (smallEtaleTopology (Spec (.of R))) (Type (max (u + 1) v)))
      (presheafFiberClosedPointIsoSections.{u, v} x hx)).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R))) (Type (max (u + 1) v))
      (isTerminalEtaleMkId (Spec (.of R)))).symm

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- **Stacks Project, Tag 03Q9 for sheaves of sets in degree zero, over a strictly henselian
local base.** For `R` strictly henselian local and `x` a geometric point of `Spec R` above the
closed point, the stalk at `x` of a direct image along `f : X ⟶ Spec R` is the set of global
sections on `X`, naturally in the sheaf of sets. -/
def pushforwardSheafFiberClosedPointIsoGamma :
    (smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
          (smallEtaleTopology (Spec (.of R))) (smallEtaleTopology X) ⋙
        (pointSmallEtale x).sheafFiber ≅
      Sheaf.Γ (smallEtaleTopology X) (Type (max (u + 1) v)) :=
  Functor.isoWhiskerLeft _ (sheafFiberClosedPointIsoGamma.{u, v} x hx) ≪≫
    smallEtalePushforwardGammaIso.{u, v} f

/-- **The stalk of a direct image along a proper morphism over a strictly henselian local base
is the set of global sections on the closed fibre**, granted compatible presenting families.
For `R` strictly henselian local, `f : X ⟶ Spec R` proper and `x` a geometric point of `Spec R`
above the closed point, `(f_*F)_x = Γ(X₀, F|_{X₀})` with `X₀ = X ×_{Spec R} Spec κ(R)`,
naturally in the sheaf of sets `F`.

The first factor is Tag 03Q9 for sheaves of sets over a strictly henselian base, which is
unconditional; the second is [Stacks, Tag 0A3S], whose surjectivity half is the carried
hypothesis `hcompat` of
`Stacks.EtaleCohomology.isIso_globalSectionsComparison_closedFibre_of_henselianLocalRing`. -/
def pushforwardSheafFiberClosedPointIsoClosedFibreGamma [IsProper f]
    (hcompat : ∀ (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
      (t : ((smallEtaleInverseImage.{u, v} (closedFibreInclusion R f)).obj F).obj.obj
        (op (terminal (closedFibre R f).Etale))),
      ∃ (α : Type (u + 1)) (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j))),
        (⨆ j, smallEtaleImage (W j)) = ⊤ ∧ SmallEtaleCompatible F W s ∧
          ∀ j, ((smallEtaleInverseImage.{u, v} (closedFibreInclusion R f)).obj F).obj.map
                (terminal.from ((smallEtaleBaseChange
                  (closedFibreInclusion R f)).obj (W j))).op t
              = smallEtaleSectionPullback.{u, v} (closedFibreInclusion R f) F (W j) (s j)) :
    (smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
          (smallEtaleTopology (Spec (.of R))) (smallEtaleTopology X) ⋙
        (pointSmallEtale x).sheafFiber ≅
      smallEtaleInverseImage.{u, v} (closedFibreInclusion R f) ⋙
        Sheaf.Γ (smallEtaleTopology (closedFibre R f)) (Type (max (u + 1) v)) :=
  letI := isIso_globalSectionsComparison_closedFibre_of_henselianLocalRing.{u, v} R f hcompat
  pushforwardSheafFiberClosedPointIsoGamma.{u, v} x hx f ≪≫
    asIso (globalSectionsSmallEtaleInverseImageComparison.{u, v}
      (closedFibreInclusion R f)).val

/-- The composition isomorphism for inverse images of sheaves of sets on small étale sites:
inverse image along `f` after inverse image along `g` is inverse image along `f ≫ g`, as the
mate of `Stacks.EtaleCohomology.smallEtalePushforwardCompIso`. -/
def smallEtaleInverseImageComp {T T' T'' : Scheme.{u}} (g : T ⟶ T') (h : T' ⟶ T'') :
    smallEtaleInverseImage.{u, v} h ⋙ smallEtaleInverseImage.{u, v} g ≅
      smallEtaleInverseImage.{u, v} (g ≫ h) :=
  Adjunction.leftAdjointCompIso (smallEtaleInverseImageAdjunction.{u, v} h)
    (smallEtaleInverseImageAdjunction.{u, v} g)
    (smallEtaleInverseImageAdjunction.{u, v} (g ≫ h))
    (smallEtalePushforwardCompIso.{u, v} g h)

variable (Ω) [Algebra (IsLocalRing.ResidueField R) Ω]

omit [IsAlgClosed Ω] in
/-- **The geometric fibre of `f` is the base change of its closed fibre along the residue field
extension.** Projecting `(X ×_{Spec R} Spec κ(R)) ×_{Spec κ(R)} Spec Ω` to `X` is, through the
canonical identification of that scheme with `X ×_{Spec R} Spec Ω`, the projection of the
geometric fibre at the point `Spec Ω ⟶ Spec κ(R) ⟶ Spec R`. -/
theorem closedFibreBaseChange_fst_comp_closedFibreInclusion :
    pullback.fst (closedFibreProjection R f)
          (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) Ω))) ≫
        closedFibreInclusion R f =
      (pullbackLeftPullbackSndIso f (residueFieldPoint R)
            (Spec.map (CommRingCat.ofHom
              (algebraMap (IsLocalRing.ResidueField R) Ω)))).hom ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom
          (algebraMap (IsLocalRing.ResidueField R) Ω)) ≫ residueFieldPoint R) :=
  (pullbackLeftPullbackSndIso_hom_fst f (residueFieldPoint R) _).symm

/-- **The stalk of a direct image along a proper morphism over a strictly henselian local base is
the set of global sections over the geometric fibre**, granted compatible presenting families.
For `R` strictly henselian local with residue field `κ(R)`, `f : X ⟶ Spec R` proper, `Ω` an
extension of `κ(R)` and `x` a geometric point of `Spec R` above the closed point,
`(f_*F)_x = Γ(X_Ω, F|_{X_Ω})` with `X_Ω = (X ×_{Spec R} Spec κ(R)) ×_{Spec κ(R)} Spec Ω`,
naturally in the sheaf of sets `F`.

This is the whole of the proof of [Stacks, Tag 0A3T] except for the reduction of a general base
to the strict henselization, which is Tag 03Q9 and is absent: Tag 03Q9 over the already strictly
henselian base is `pushforwardSheafFiberClosedPointIsoGamma`, Tag 0A3S is the hypothesis
`hcompat`, and the extension of the separably closed residue field to `Ω` is [Stacks, Tag 0A3I].
That the right-hand side is the geometric fibre of `f` at `x` is
`closedFibreBaseChange_fst_comp_closedFibreInclusion`, for `x` the composite point. -/
@[stacks 0A3T "conditional on the base being `Spec R` for a strictly henselian local ring `R`, \
the reduction of a general base to the strict henselization being Tag 03Q9 for sheaves of sets, \
which is absent; and carrying `hcompat`, the hypothesis of the library's Tag 0A3S"]
def pushforwardSheafFiberClosedPointIsoGeometricFibreGamma [IsProper f]
    (hcompat : ∀ (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
      (t : ((smallEtaleInverseImage.{u, v} (closedFibreInclusion R f)).obj F).obj.obj
        (op (terminal (closedFibre R f).Etale))),
      ∃ (α : Type (u + 1)) (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j))),
        (⨆ j, smallEtaleImage (W j)) = ⊤ ∧ SmallEtaleCompatible F W s ∧
          ∀ j, ((smallEtaleInverseImage.{u, v} (closedFibreInclusion R f)).obj F).obj.map
                (terminal.from ((smallEtaleBaseChange
                  (closedFibreInclusion R f)).obj (W j))).op t
              = smallEtaleSectionPullback.{u, v} (closedFibreInclusion R f) F (W j) (s j)) :
    (smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
          (smallEtaleTopology (Spec (.of R))) (smallEtaleTopology X) ⋙
        (pointSmallEtale x).sheafFiber ≅
      smallEtaleInverseImage.{u, v}
          (pullback.fst (closedFibreProjection R f)
            (Spec.map (CommRingCat.ofHom
              (algebraMap (IsLocalRing.ResidueField R) Ω))) ≫ closedFibreInclusion R f) ⋙
        Sheaf.Γ (smallEtaleTopology (pullback (closedFibreProjection R f)
          (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) Ω)))))
          (Type (max (u + 1) v)) :=
  pushforwardSheafFiberClosedPointIsoClosedFibreGamma.{u, v} x hx f hcompat ≪≫
    Functor.isoWhiskerLeft _ (globalSectionsSmallEtaleInverseImageIso_of_isSepClosed.{u, v}
      (IsLocalRing.ResidueField R) Ω (closedFibreProjection R f)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (smallEtaleInverseImageComp.{u, v} _ _) _

end StrictlyHenselianBase

end Stacks.EtaleCohomology

end
