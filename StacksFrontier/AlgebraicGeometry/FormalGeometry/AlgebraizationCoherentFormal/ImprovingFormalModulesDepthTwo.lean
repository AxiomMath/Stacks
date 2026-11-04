module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModules
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtension
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovement

/-!
# Improving a coherent formal module to depth two along a closed subset

Let `X` be a Noetherian scheme, let `T ⊆ X` be stable under specialization, let `T' ⊆ X` be
closed and let `(ℱₙ)` be an inverse system of coherent `𝒪_X`-modules.  Dividing out the
sections supported on `T` gives the system `(ℱ'ₙ)`; extending each `ℱ'ₙ` across `T'` to depth
two gives a family `ℱ''ₙ`, and that family is again an inverse system: a depth-two extension
along a closed subset is a universal arrow, so a map out of `ℱ'ₘ` into any `ℱ''ₙ` factors
uniquely through `ℱ'ₘ ⟶ ℱ''ₘ`.  The resulting system carries a canonical map from `(ℱₙ)`, and
its terms have depth at least one along `T` and depth at least two along `T'`.

## Main definitions

* `Stacks.Algebraization.DepthTwoImprovement`: a termwise depth-two extension of `(ℱ'ₙ)`.
* `Stacks.Algebraization.depthTwoImprovedSystem`: the inverse system `(ℱ''ₙ)`.
* `Stacks.Algebraization.toDepthTwoImprovedSystem`: the canonical map `(ℱₙ) ⟶ (ℱ''ₙ)`.

## Main results

* `Stacks.Algebraization.bijective_precomp_of_isDepthTwoExtension`: a depth-two extension along
  a closed subset is universal among maps into modules of depth at least two along that subset.
* `Stacks.Algebraization.depth_stalk_depthTwoImprovedSystem`: every term of `(ℱ''ₙ)` has depth
  at least one at each point of `T` and depth at least two at each point of `T'`.

## Implementation notes

The universal property is the Hartogs isomorphism `ℋ ≅ j_*(ℋ|_V)` of [Stacks, Tag 0E9I] for
`V = X ∖ T'` and a module `ℋ` of depth at least two along `T'`, which makes restriction to `V`
a bijection on morphisms into `ℋ`, combined with the restriction of a depth-two extension to
`V` being an isomorphism.  Both are assembled from one categorical statement about an
adjunction `L ⊣ R`: precomposition with a morphism that `L` inverts is bijective on morphisms
into an object at which the unit is invertible.

Closedness of `T'` is what makes `X ∖ T'` open, and it is the only place the hypothesis is
used; a closed subset is in particular stable under specialization, so this is a restriction of
the source's hypothesis on `T'` and not an extra one.  Without it the source replaces `V` by a
family of opens avoiding one point at a time, which needs the stabilization of the system of
pushforwards that this library does not have.

The termwise depth-two extensions are data: their existence is the existence half of
[Stacks, Tag 0EI3], which this library carries only conditionally.

### No unrestricted `@[stacks 0EJF]`

Only conclusions (1) and (2) of the source are proved here, and under two restrictions
recorded in the attribute: `T'` is closed, and the termwise depth-two extensions are
hypotheses rather than constructed.  Conclusions (3) and (4) — that `(ℱ''ₙ)` is
pro-isomorphic to an object of `Coh(X, ℐ)` and that the induced morphism has kernel and
cokernel annihilated by a power of `ℐ` — rest on the essential-constancy assertion of
[Stacks, Tag 0EIE], which this library carries only as a hypothesis of its consequences.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

/-! ### The universal property of a depth-two extension along a closed subset -/

/-- For an adjunction `L ⊣ R`, precomposition with a morphism that `L` inverts is a bijection
on morphisms into an object at which the unit of the adjunction is invertible. -/
public theorem bijective_precomp_of_adjunction {C : Type*} {D : Type*} [Category C]
    [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A B K : C} (φ : A ⟶ B)
    (hφ : IsIso (L.map φ)) (hK : IsIso (adj.unit.app K)) :
    Function.Bijective fun l : B ⟶ K => φ ≫ l := by
  have := hK
  have hmap : ∀ Z : C, Function.Bijective fun l : Z ⟶ K => L.map l := by
    intro Z
    have hpost : Function.Bijective fun l : Z ⟶ K => l ≫ adj.unit.app K :=
      ⟨fun _ _ h => (cancel_mono (adj.unit.app K)).mp h,
        fun m => ⟨m ≫ inv (adj.unit.app K), by simp⟩⟩
    have key : (fun l : Z ⟶ K => L.map l) =
        (adj.homEquiv Z (L.obj K)).symm ∘ fun l : Z ⟶ K => l ≫ adj.unit.app K := by
      funext l
      refine (adj.homEquiv Z (L.obj K)).injective ?_
      change adj.homEquiv Z (L.obj K) (L.map l) =
        adj.homEquiv Z (L.obj K) ((adj.homEquiv Z (L.obj K)).symm (l ≫ adj.unit.app K))
      rw [Equiv.apply_symm_apply]
      exact (adj.unit.naturality l).symm
    rw [key]
    exact (adj.homEquiv Z (L.obj K)).symm.bijective.comp hpost
  have := hφ
  refine ⟨?_, ?_⟩
  · intro l₁ l₂ h
    refine (hmap B).1 ?_
    change L.map l₁ = L.map l₂
    refine (cancel_epi (L.map φ)).mp ?_
    rw [← L.map_comp, ← L.map_comp]
    exact congrArg L.map h
  · intro g
    obtain ⟨l, hl⟩ := (hmap B).2 (inv (L.map φ) ≫ L.map g)
    have hl' : L.map l = inv (L.map φ) ≫ L.map g := hl
    refine ⟨l, (hmap A).1 ?_⟩
    change L.map (φ ≫ l) = L.map g
    rw [L.map_comp, hl', IsIso.hom_inv_id_assoc]

/-- **A depth-two extension along a closed subset is universal.** If `φ : ℱ ⟶ 𝒢` is an
isomorphism on the stalks away from a closed subset `T'` and `𝒦` is a coherent module whose
stalks have depth at least two at the points of `T'`, then every map `ℱ ⟶ 𝒦` factors uniquely
through `φ`. -/
public theorem bijective_precomp_of_isDepthTwoExtension {X : Scheme.{u}} [IsNoetherian X]
    {T' : Set X} (hT' : IsClosed T') {F G : X.Modules} (φ : F ⟶ G)
    (hφ : IsDepthTwoExtension T' φ) (K : X.Modules) [K.IsCoherent]
    (hK : ∀ x : X, x ∈ T' →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) K.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) K.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) K.val.presheaf x)) :
    Function.Bijective fun l : G ⟶ K => φ ≫ l := by
  obtain ⟨V, hV⟩ : ∃ V : X.Opens, (V : Set X) = T'ᶜ := ⟨⟨T'ᶜ, hT'.isOpen_compl⟩, rfl⟩
  have hunitP : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app K) :=
    isIso_unit_restrict_pushforward_of_depth_ge_two X K V fun x hx =>
      hK x (by simpa [hV] using hx)
  have hunitL : IsIso ((Scheme.Modules.restrictAdjunction V.ι).unit.app K) := by
    have hcomp : (Scheme.Modules.restrictAdjunction V.ι).unit.app K ≫
        (Scheme.Modules.pushforward V.ι).map
          ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app K) =
        (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app K :=
      Adjunction.unit_leftAdjointUniq_hom_app _ _ K
    have : IsIso ((Scheme.Modules.restrictAdjunction V.ι).unit.app K ≫
        (Scheme.Modules.pushforward V.ι).map
          ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app K)) := by
      rw [hcomp]; exact hunitP
    exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward V.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app K))
  have hisoV : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ) := by
    refine isIso_restrict_of_forall_stalkAb_isIso V φ fun x hx => ?_
    rw [hV] at hx
    exact isIso_stalkAb_of_isIso_stalkMap φ x (hφ.2.1 x hx)
  exact bijective_precomp_of_adjunction (Scheme.Modules.restrictAdjunction V.ι) φ hisoV hunitL

/-! ### The depth-two improvement of an inverse system -/

variable {X : Scheme.{u}} [IsNoetherian X] {T T' : Set X}
  {hT : StableUnderSpecialization T} {F : ℕᵒᵖ ⥤ X.Modules}
  [∀ n : ℕᵒᵖ, (F.obj n).IsCoherent]

/-- A termwise depth-two extension of the system `(ℱ'ₙ)` of depth-one quotients of `(ℱₙ)`
along `T`: for each `n` a coherent module `ℱ''ₙ` and a map `ℱ'ₙ ⟶ ℱ''ₙ` which is an isomorphism
on the stalks away from `T'` and whose target has depth at least two along `T'`. -/
public structure DepthTwoImprovement (T T' : Set X) (hT : StableUnderSpecialization T)
    (F : ℕᵒᵖ ⥤ X.Modules) [∀ n : ℕᵒᵖ, (F.obj n).IsCoherent] where
  /-- The depth-two extension `ℱ''ₙ` of the `n`-th term of the improved system. -/
  term : ℕᵒᵖ → X.Modules
  /-- The extension map `ℱ'ₙ ⟶ ℱ''ₙ`. -/
  extend : ∀ n : ℕᵒᵖ, (improvedSystem T hT F).obj n ⟶ term n
  /-- Every extension map is a depth-two extension along `T'`. -/
  extend_isDepthTwoExtension : ∀ n : ℕᵒᵖ, IsDepthTwoExtension T' (extend n)

/-- Precomposition with the depth-two extension at `m` is a bijection onto the morphisms from
`ℱ'ₘ` to the depth-two extension at `n`. -/
public theorem bijective_precomp_extend (hT' : IsClosed T')
    (S : DepthTwoImprovement T T' hT F) (m n : ℕᵒᵖ) :
    Function.Bijective fun l : S.term m ⟶ S.term n => S.extend m ≫ l :=
  letI : (S.term n).IsCoherent := (S.extend_isDepthTwoExtension n).1
  bijective_precomp_of_isDepthTwoExtension hT' (S.extend m)
    (S.extend_isDepthTwoExtension m) (S.term n) (S.extend_isDepthTwoExtension n).2.2

/-- The transition map `ℱ''ₘ ⟶ ℱ''ₙ` induced by a transition map `ℱₘ ⟶ ℱₙ`, obtained from the
universal property of the depth-two extension at `m`. -/
public def depthTwoImprovedMap (hT' : IsClosed T') (S : DepthTwoImprovement T T' hT F)
    {m n : ℕᵒᵖ} (f : m ⟶ n) : S.term m ⟶ S.term n :=
  (Equiv.ofBijective _ (bijective_precomp_extend hT' S m n)).symm
    ((improvedSystem T hT F).map f ≫ S.extend n)

/-- The induced transition map of depth-two extensions is compatible with the extension maps. -/
public theorem extend_comp_depthTwoImprovedMap (hT' : IsClosed T')
    (S : DepthTwoImprovement T T' hT F) {m n : ℕᵒᵖ} (f : m ⟶ n) :
    S.extend m ≫ depthTwoImprovedMap hT' S f = (improvedSystem T hT F).map f ≫ S.extend n :=
  (Equiv.ofBijective _ (bijective_precomp_extend hT' S m n)).apply_symm_apply _

/-- Two maps out of a depth-two extension agree as soon as they agree after the extension
map. -/
public theorem depthTwoImproved_hom_ext (hT' : IsClosed T')
    (S : DepthTwoImprovement T T' hT F) {m n : ℕᵒᵖ} {l₁ l₂ : S.term m ⟶ S.term n}
    (h : S.extend m ≫ l₁ = S.extend m ≫ l₂) : l₁ = l₂ :=
  (bijective_precomp_extend hT' S m n).1 h

/-- The inverse system `(ℱ''ₙ)` obtained by extending each term of `(ℱ'ₙ)` across `T'` to depth
two. -/
public def depthTwoImprovedSystem (hT' : IsClosed T') (S : DepthTwoImprovement T T' hT F) :
    ℕᵒᵖ ⥤ X.Modules where
  obj n := S.term n
  map f := depthTwoImprovedMap hT' S f
  map_id n := by
    refine depthTwoImproved_hom_ext hT' S ?_
    rw [extend_comp_depthTwoImprovedMap hT' S (CategoryStruct.id n),
      (improvedSystem T hT F).map_id, Category.id_comp, Category.comp_id]
  map_comp {l m n} f g := by
    refine depthTwoImproved_hom_ext hT' S ?_
    rw [extend_comp_depthTwoImprovedMap hT' S (f ≫ g), (improvedSystem T hT F).map_comp,
      Category.assoc, ← Category.assoc (S.extend l), extend_comp_depthTwoImprovedMap hT' S f,
      Category.assoc, extend_comp_depthTwoImprovedMap hT' S g]

@[simp]
public theorem depthTwoImprovedSystem_obj (hT' : IsClosed T')
    (S : DepthTwoImprovement T T' hT F) (n : ℕᵒᵖ) :
    (depthTwoImprovedSystem hT' S).obj n = S.term n :=
  rfl

/-- The canonical map `(ℱₙ) ⟶ (ℱ''ₙ)` of inverse systems: the depth-one quotient map followed
by the depth-two extension. -/
public def toDepthTwoImprovedSystem (hT' : IsClosed T') (S : DepthTwoImprovement T T' hT F) :
    F ⟶ depthTwoImprovedSystem hT' S where
  app n := (toImprovedSystem T hT F).app n ≫ S.extend n
  naturality m n f := by
    have hnat : F.map f ≫ (toImprovedSystem T hT F).app n =
        (toImprovedSystem T hT F).app m ≫ (improvedSystem T hT F).map f :=
      (toImprovedSystem T hT F).naturality f
    calc F.map f ≫ ((toImprovedSystem T hT F).app n ≫ S.extend n)
        = (F.map f ≫ (toImprovedSystem T hT F).app n) ≫ S.extend n :=
          (Category.assoc _ _ _).symm
      _ = ((toImprovedSystem T hT F).app m ≫ (improvedSystem T hT F).map f) ≫ S.extend n := by
          rw [hnat]
      _ = (toImprovedSystem T hT F).app m ≫ ((improvedSystem T hT F).map f ≫ S.extend n) :=
          Category.assoc _ _ _
      _ = (toImprovedSystem T hT F).app m ≫ (S.extend m ≫ depthTwoImprovedMap hT' S f) := by
          rw [extend_comp_depthTwoImprovedMap hT' S f]
      _ = ((toImprovedSystem T hT F).app m ≫ S.extend m) ≫ depthTwoImprovedMap hT' S f :=
          (Category.assoc _ _ _).symm

@[simp]
public theorem toDepthTwoImprovedSystem_app (hT' : IsClosed T')
    (S : DepthTwoImprovement T T' hT F) (n : ℕᵒᵖ) :
    (toDepthTwoImprovedSystem hT' S).app n =
      (toImprovedSystem T hT F).app n ≫ S.extend n :=
  rfl

/-- **Stacks Project, Tag 0EJF, conclusions (1) and (2).** Every term of the depth-two improved
system has depth at least one at each point of `T` and depth at least two at each point of
`T'`. -/
@[stacks 0EJF "conclusions (1) and (2), for T' closed and with the termwise depth-two \
extensions as data; conclusions (3) and (4) rest on the essential-constancy assertion of Tag \
0EIE, which this library carries only as a hypothesis"]
public theorem depth_stalk_depthTwoImprovedSystem (S : DepthTwoImprovement T T' hT F)
    (n : ℕᵒᵖ) (x : X) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (S.term n).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (S.term n).val x
    (x ∈ T → (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) (S.term n).val.presheaf x)) ∧
      (x ∈ T' → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) (S.term n).val.presheaf x)) := by
  refine ⟨fun hx => ?_, fun hx => (S.extend_isDepthTwoExtension n).2.2 x hx⟩
  by_cases hx' : x ∈ T'
  · exact le_trans (by norm_num) ((S.extend_isDepthTwoExtension n).2.2 x hx')
  · rw [← depth_stalk_eq_of_isIso_stalkMap (S.extend n) x
      ((S.extend_isDepthTwoExtension n).2.1 x hx')]
    exact one_le_depth_improvedSystem_stalk T hT F n x hx

end Stacks.Algebraization

end
