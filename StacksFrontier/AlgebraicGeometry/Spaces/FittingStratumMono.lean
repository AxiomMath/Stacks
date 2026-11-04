module

public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStrata
public import StacksFrontier.CategoryTheory.Sites.CoproductUniversality

/-!
# The structural morphism of the disjoint union of the Fitting rank strata is a monomorphism

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`X ⊇ Z_0 ⊇ Z_1 ⊇ …` be a decreasing chain of closed subspaces of `X`, with strata
`X_r = Z_{r-1} \ Z_r`.  This file proves that the structural morphism
`π : X' = ∐_{r ≥ 0} X_r ⟶ X` of
`StacksFrontier/AlgebraicGeometry/Spaces/FittingRankStrata.lean` is a **monomorphism**.

The point of the statement is that it makes the factorisation problem solved by the flatness
clause of Stacks 0CZA *local on the test object* with no further input: the set of morphisms
`h : T' ⟶ X'` over a fixed `a : T' ⟶ X` has at most one element for every `T'`, so local
factorisations are automatically compatible and glue, and the glued factorisation is unique.
In particular a cover of the test object by the pieces over which a rank is constant does
**not** have to be made disjoint.

## Main results

* `CategoryTheory.Sheaf.injective_app_of_isColimit_cofan`: **a morphism out of a coproduct of
  sheaves of sets is injective on sections** as soon as each leg becomes injective on sections
  after composing with it and any two sections of distinct legs with a common image live over
  an object covered by the empty sieve.
* `CategoryTheory.Sheaf.mono_of_isColimit_cofan`: the same hypotheses make the morphism a
  monomorphism of sheaves.
* `CategoryTheory.Presieve.IsSheaf.existsUnique_section_of_injective`: a factorisation through a
  morphism of sheaves which is injective on sections is unique, and exists as soon as it exists
  locally — with no compatibility condition on the local factorisations.
* `AlgebraicGeometry.Space.injective_app_fittingRankStratificationHom`,
  `AlgebraicGeometry.Space.mono_hom_fittingRankStratificationHom` and
  `AlgebraicGeometry.Space.mono_fittingRankStratificationHom`: **`π : ∐_r X_r ⟶ X` is a
  monomorphism**, for the strata of any decreasing chain of closed subspaces.
* `AlgebraicGeometry.Space.existsUnique_lift_fittingRankStratification_of_local` and
  `AlgebraicGeometry.Space.existsUnique_lift_fittingRankStratification_of_openCover`:
  **factoring a section of `X` through `X'` is a local problem on the test object**, over a
  covering sieve and over a jointly surjective family of open subobjects respectively.  The
  members of the family are not asked to be disjoint and the local factorisations are not asked
  to be compatible.

## Implementation notes

The abstract statement runs on joint local surjectivity of the legs of a coproduct cocone of
sheaves, `CategoryTheory.Sheaf.sieveOfSection_iSup_range_mem`, which holds on an arbitrary
site and needs no left exactness of sheafification: two sections of the vertex with the same
image in the target are each, locally on a covering sieve, in the image of some leg, and the
intersection of the two covering sieves is covering.  Over an object of that intersection the
two sections come from legs with indices `i` and `j`; if `i = j` the composite with the
morphism is injective and they agree, and if `i ≠ j` the object is covered by the empty sieve,
where a sheaf has at most one section.  No decomposition of the object into open pieces is
used, and therefore no fibre product in the site either — only the sieve-level statement, which
is why the lemma is available for a general site.

For the strata the two hypotheses are exactly the two facts already proved about them: the
composite of the `r`-th leg with `π` is the inclusion `X_r ⟶ X` of a subfunctor, whose sections
are a subtype and whose action on them is the coercion; and two distinct strata meet inside the
sheafification of the bottom subfunctor by
`AlgebraicGeometry.Space.fittingRankStratum_inf_le_sheafify_bot`, which on an object carrying a
section of the meet forces the empty sieve to cover it.

Antitonicity of the chain is the only hypothesis, and it is what the disjointness of the strata
needs; on the Fitting chain of a module it is supplied by
`AlgebraicGeometry.Space.antitone_of_definingIdealSheaf_eq_fittingIdeal`.

## References

* [Stacks Project, Tag 0CZA](https://stacks.math.columbia.edu/tag/0CZA)
* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

/-! ### A morphism out of a coproduct of locally disjoint sheaves -/

section Abstract

variable {C : Type u} [Category.{v} C]

/-- **A morphism out of a coproduct of sheaves of sets is injective on sections** as soon as
each leg of the coproduct becomes injective on sections after composing with it, and any two
sections of two distinct legs with the same image live over an object covered by the empty
sieve.

The legs are jointly locally surjective on an arbitrary site
(`CategoryTheory.Sheaf.sieveOfSection_iSup_range_mem`), so two sections of the vertex with the
same image agree after restriction along a covering sieve, and a sheaf is separated for a
covering sieve. -/
theorem Sheaf.injective_app_of_isColimit_cofan {I : Type*} (J : GrothendieckTopology C)
    {F : I → Sheaf J (Type v)} {P Q : Sheaf J (Type v)} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (φ : P ⟶ Q)
    (hinj : ∀ (i : I) (Z : C), Function.Injective fun z : (F i).obj.obj (op Z) =>
      φ.hom.app (op Z) ((ι i).hom.app (op Z) z))
    (hdisj : ∀ i j : I, i ≠ j → ∀ (Z : C) (z : (F i).obj.obj (op Z))
      (z' : (F j).obj.obj (op Z)),
      φ.hom.app (op Z) ((ι i).hom.app (op Z) z) =
        φ.hom.app (op Z) ((ι j).hom.app (op Z) z') → (⊥ : Sieve Z) ∈ J Z)
    (W : C) : Function.Injective (φ.hom.app (op W)) := by
  intro x y hxy
  have hPsheaf : Presieve.IsSheaf J P.obj := (isSheaf_iff_isSheaf_of_type J _).1 P.property
  have hx := Sheaf.sieveOfSection_iSup_range_mem J ι hP (op W) x
  have hy := Sheaf.sieveOfSection_iSup_range_mem J ι hP (op W) y
  refine ((hPsheaf _ (J.intersection_covering hx hy)).isSeparatedFor).ext ?_
  intro T t ht
  have htx : P.obj.map t.op x ∈ (⨆ i, Subfunctor.range (ι i).hom).obj (op T) := ht.1
  have hty : P.obj.map t.op y ∈ (⨆ i, Subfunctor.range (ι i).hom).obj (op T) := ht.2
  rw [Subfunctor.iSup_obj, Set.mem_iUnion] at htx hty
  obtain ⟨i, z, hz⟩ := htx
  obtain ⟨j, z', hz'⟩ := hty
  have hkey : φ.hom.app (op T) ((ι i).hom.app (op T) z) =
      φ.hom.app (op T) ((ι j).hom.app (op T) z') := by
    rw [hz, hz', NatTrans.naturality_apply φ.hom t.op x,
      NatTrans.naturality_apply φ.hom t.op y, hxy]
  rcases eq_or_ne i j with rfl | hij
  · rw [← hz, ← hz', hinj i T hkey]
  · exact (hPsheaf.subsingleton_obj_of_bot_mem _ (hdisj i j hij T z z' hkey)).elim _ _

/-- **A factorisation through a morphism of sheaves injective on sections is unique, and exists
as soon as it exists locally.**  No compatibility hypothesis is asked of the local
factorisations: injectivity on sections makes any two of them agree wherever both are defined,
so the chosen family is automatically compatible and amalgamates. -/
theorem Presieve.IsSheaf.existsUnique_section_of_injective (J : GrothendieckTopology C)
    {H K : Cᵒᵖ ⥤ Type w} (hH : Presieve.IsSheaf J H) (hK : Presieve.IsSheaf J K) (φ : H ⟶ K)
    (hinj : ∀ U : Cᵒᵖ, Function.Injective (φ.app U)) {T : C} {R : Sieve T} (hR : R ∈ J T)
    (a : K.obj (op T))
    (hloc : ∀ (Y : C) (f : Y ⟶ T), R.arrows f →
      ∃ y : H.obj (op Y), φ.app (op Y) y = K.map f.op a) :
    ∃! τ : H.obj (op T), φ.app (op T) τ = a := by
  choose y hy using hloc
  have hcompat : Presieve.FamilyOfElements.Compatible
      (show Presieve.FamilyOfElements H R.arrows from fun Y f hf => y Y f hf) := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y W f g hf
    refine hinj (op W) ?_
    rw [hy W (g ≫ f) (R.downward_closed hf g), NatTrans.naturality_apply φ g.op (y Y f hf),
      hy Y f hf, ← Functor.map_comp_apply, ← op_comp]
  obtain ⟨τ, hτ, -⟩ := hH R hR _ hcompat
  have hφτ : φ.app (op T) τ = a := by
    refine ((hK R hR).isSeparatedFor).ext ?_
    intro Y f hf
    rw [← NatTrans.naturality_apply φ f.op τ, hτ f hf]
    exact hy Y f hf
  exact ⟨τ, hφτ, fun τ' hτ' => hinj (op T) (hτ'.trans hφτ.symm)⟩

/-- **A morphism out of a coproduct of sheaves of sets is a monomorphism** under the hypotheses
of `CategoryTheory.Sheaf.injective_app_of_isColimit_cofan`. -/
theorem Sheaf.mono_of_isColimit_cofan {I : Type*} (J : GrothendieckTopology C)
    {F : I → Sheaf J (Type v)} {P Q : Sheaf J (Type v)} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (φ : P ⟶ Q)
    (hinj : ∀ (i : I) (Z : C), Function.Injective fun z : (F i).obj.obj (op Z) =>
      φ.hom.app (op Z) ((ι i).hom.app (op Z) z))
    (hdisj : ∀ i j : I, i ≠ j → ∀ (Z : C) (z : (F i).obj.obj (op Z))
      (z' : (F j).obj.obj (op Z)),
      φ.hom.app (op Z) ((ι i).hom.app (op Z) z) =
        φ.hom.app (op Z) ((ι j).hom.app (op Z) z') → (⊥ : Sieve Z) ∈ J Z) :
    Mono φ :=
  Sheaf.mono_of_injective φ fun U =>
    Sheaf.injective_app_of_isColimit_cofan J ι hP φ hinj hdisj U.unop

end Abstract

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### The structural morphism of the disjoint union of the strata -/

/-- **The structural morphism `π : X' = ∐_{r ≥ 0} X_r ⟶ X` of the disjoint union of the strata
of a decreasing chain of closed subspaces is injective on sections.**

The composite of the `r`-th leg of the coproduct with `π` is the inclusion of the subfunctor
`X_r` in `X`, which acts on sections as the coercion out of a subtype; and a section of `X` in
two distinct strata at once lies in the sheafification of the bottom subfunctor by
`AlgebraicGeometry.Space.fittingRankStratum_inf_le_sheafify_bot`, which forces the empty sieve
to cover the object it lives on. -/
theorem injective_app_fittingRankStratificationHom (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : Antitone fun r ↦ (Z r).1) (W : BigFppfOver B S hS) :
    Function.Injective ((fittingRankStratificationHom B S hS X Z).hom.app (op W)) := by
  let Φ := algebraicSpacesToSheaf B S hS
  let leg : ∀ r : ℕ, fittingRankStratumSpace B S hS X Z r ⟶
      fittingRankStratification B S hS X Z := fun r ↦
    Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r
  have hsheaf : IsColimit (Cofan.mk (Φ.obj (fittingRankStratification B S hS X Z))
      fun r ↦ Φ.map (leg r)) :=
    isColimitCofanMkObjOfIsColimit Φ _ leg (coproductIsCoproduct _)
  -- the `r`-th leg followed by `π` is the inclusion of the `r`-th stratum
  have hres : ∀ r : ℕ, (Φ.map (leg r)).hom ≫
      (Φ.map (fittingRankStratificationHom B S hS X Z)).hom =
      (fittingRankStratum B S hS X Z r).ι := fun r ↦
    congrArg (fun k : fittingRankStratumSpace B S hS X Z r ⟶ X ↦ k.hom)
      ((isAlgebraicSpace_fittingRankStratification B S hS X Z).2 r)
  have hresapp : ∀ (r : ℕ) (T : BigFppfOver B S hS)
      (z : (fittingRankStratum B S hS X Z r).toFunctor.obj (op T)),
      (Φ.map (fittingRankStratificationHom B S hS X Z)).hom.app (op T)
          ((Φ.map (leg r)).hom.app (op T) z) = (z : X.1.obj (op T)) := fun r T z ↦
    congrArg (fun k : (fittingRankStratum B S hS X Z r).toFunctor ⟶ X.1 ↦ k.app (op T) z) (hres r)
  refine Sheaf.injective_app_of_isColimit_cofan (BigFppfOver.topology B S hS)
    (fun r ↦ Φ.map (leg r)) hsheaf (Φ.map (fittingRankStratificationHom B S hS X Z))
    (fun r T z z' h ↦ ?_) (fun r s hrs T z z' h ↦ ?_) W
  · exact Subtype.ext ((hresapp r T z).symm.trans (h.trans (hresapp r T z')))
  · have hzz : z.1 = z'.1 := (hresapp r T z).symm.trans (h.trans (hresapp s T z'))
    exact (AlgebraicGeometry.mem_sheafify_bot_iff (BigFppfOver.topology B S hS) z.1).1
      (fittingRankStratum_inf_le_sheafify_bot B S hS X Z hZ hrs (op T) ⟨z.2, hzz ▸ z'.2⟩)

/-- **The structural morphism `π : X' = ∐_{r ≥ 0} X_r ⟶ X` of the disjoint union of the strata
of a decreasing chain of closed subspaces is a monomorphism of presheaves.** -/
theorem mono_hom_fittingRankStratificationHom (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : Antitone fun r ↦ (Z r).1) :
    Mono (fittingRankStratificationHom B S hS X Z).hom :=
  (NatTrans.mono_iff_mono_app _).2 fun U ↦
    (mono_iff_injective _).2 (injective_app_fittingRankStratificationHom B S hS X Z hZ U.unop)

/-- **The structural morphism `π : X' = ∐_{r ≥ 0} X_r ⟶ X` of the disjoint union of the strata
of a decreasing chain of closed subspaces is a monomorphism of algebraic spaces.**

This is what makes the factorisation problem of the flatness clause of Stacks 0CZA local on the
test object: over a fixed morphism to `X` there is at most one morphism to `X'`, so local
factorisations through `X'` are compatible with no condition and glue, and the glued
factorisation is the unique one. -/
theorem mono_fittingRankStratificationHom (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : Antitone fun r ↦ (Z r).1) :
    Mono (fittingRankStratificationHom B S hS X Z) :=
  (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u ↦
      IsAlgebraicSpace B S hS F)).mono_of_mono_map
    (mono_hom_fittingRankStratificationHom B S hS X Z hZ)

/-! ### Factoring through the disjoint union is a local problem on the test object -/

/-- **A section of `X` lifts to the disjoint union `X' = ∐_{r ≥ 0} X_r`, necessarily uniquely, as
soon as it lifts after restriction along every arrow of one covering sieve.**

The local lifts are *not* asked to be compatible: by
`AlgebraicGeometry.Space.injective_app_fittingRankStratificationHom` a lift over an object is
unique, so any two of them agree wherever both are defined, and the chosen family amalgamates
over the sieve. -/
theorem existsUnique_lift_fittingRankStratification_of_local
    (Z : ℕ → ClosedSubspaces B S hS X.1) (hZ : Antitone fun r ↦ (Z r).1)
    {T : BigFppfOver B S hS} {R : Sieve T} (hR : R ∈ BigFppfOver.topology B S hS T)
    (a : X.1.obj (op T))
    (hloc : ∀ (Y : BigFppfOver B S hS) (f : Y ⟶ T), R.arrows f →
      ∃ y : (fittingRankStratification B S hS X Z).1.obj (op Y),
        (fittingRankStratificationHom B S hS X Z).hom.app (op Y) y = X.1.map f.op a) :
    ∃! τ : (fittingRankStratification B S hS X Z).1.obj (op T),
      (fittingRankStratificationHom B S hS X Z).hom.app (op T) τ = a :=
  Presieve.IsSheaf.existsUnique_section_of_injective (BigFppfOver.topology B S hS)
    ((isSheaf_iff_isSheaf_of_type _ _).1 (fittingRankStratification B S hS X Z).2.isSheaf)
    ((isSheaf_iff_isSheaf_of_type _ _).1 X.2.isSheaf)
    (fittingRankStratificationHom B S hS X Z).hom
    (fun U => injective_app_fittingRankStratificationHom B S hS X Z hZ U.unop)
    hR a hloc

/-- **A section of `X` lifts to the disjoint union `X' = ∐_{r ≥ 0} X_r`, necessarily uniquely, as
soon as it lifts over the members of one jointly surjective family of open subobjects of the
test object.**

This is the form the flatness clause of Stacks 0CZA consumes: the pieces of the test object on
which a rank of the module is constant are produced one point at a time, as basic opens, and
they are therefore *not* pairwise disjoint.  They do not have to be: the family of local lifts
needs no compatibility condition, because `π` is a monomorphism. -/
theorem existsUnique_lift_fittingRankStratification_of_openCover
    (Z : ℕ → ClosedSubspaces B S hS X.1) (hZ : Antitone fun r ↦ (Z r).1)
    {T : BigFppfOver B S hS} {κ : Type v} {W : κ → BigFppfOver B S hS} (p : ∀ k, W k ⟶ T)
    (hoi : ∀ k, AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (p k)))
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ k, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    (a : X.1.obj (op T))
    (hlift : ∀ k, ∃ y : (fittingRankStratification B S hS X Z).1.obj (op (W k)),
      (fittingRankStratificationHom B S hS X Z).hom.app (op (W k)) y = X.1.map (p k).op a) :
    ∃! τ : (fittingRankStratification B S hS X Z).1.obj (op T),
      (fittingRankStratificationHom B S hS X Z).hom.app (op T) τ = a := by
  refine existsUnique_lift_fittingRankStratification_of_local B S hS X Z hZ
    (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS p hoi hcov) a ?_
  rintro Y f ⟨Y', h, e, ⟨k⟩, hcomp⟩
  obtain ⟨yk, hyk⟩ := hlift k
  refine ⟨(fittingRankStratification B S hS X Z).1.map h.op yk, ?_⟩
  rw [NatTrans.naturality_apply (fittingRankStratificationHom B S hS X Z).hom h.op yk, hyk,
    ← Functor.map_comp_apply, ← op_comp, hcomp]

end AlgebraicGeometry.Space

end
