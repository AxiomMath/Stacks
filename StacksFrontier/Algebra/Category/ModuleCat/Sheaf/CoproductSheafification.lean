module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafification

/-!
# A coproduct of sheaves of modules is the sheafification of the objectwise coproduct

Let `R : Sheaf J RingCat` be a sheaf of rings on a site and `M : I → SheafOfModules R` a family
of sheaves of modules indexed by a type `I : Type`. The coproduct `∐ M` is taken in the
category of sheaves of modules, and for infinite `I` it is not computed objectwise, so nothing
about its sections can be read off the definition.

This file supplies the missing description and its main consequence. The coproduct
`∐ (fun i ↦ (M i).val)` taken in presheaves of modules *is* computed objectwise, and
sheafification is a left adjoint, so it carries that coproduct to the coproduct in sheaves of
modules (`coprodIso`); hence the canonical morphism from the objectwise coproduct is locally
surjective (`isLocallySurjective_toCoprod`). Since a section of the objectwise coproduct is
supported in finitely many summands, every section of `∐ M` is **locally supported in finitely
many summands** (`exists_finset_proj_eq_zero`): on a covering sieve, all but finitely many of
its components vanish.

The free case — `M` the constant family at `SheafOfModules.unit R` — is
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeSheafification.lean`.

## Main definitions

* `Stacks.SheafOfModules.CoproductSheafification.presCoprod`: the coproduct of the underlying
  presheaves of modules, which is objectwise.
* `Stacks.SheafOfModules.CoproductSheafification.toCoprod`: the canonical morphism from it to
  the presheaf underlying `∐ M`.
* `Stacks.SheafOfModules.CoproductSheafification.proj` and
  `Stacks.SheafOfModules.CoproductSheafification.presProj`: the `i`-th component of a
  coproduct, the identity on the `i`-th summand and zero on the others.

## Main results

* `Stacks.SheafOfModules.CoproductSheafification.coprodIso`: a coproduct of sheaves of modules
  is the sheafification of the coproduct of the underlying presheaves of modules.
* `Stacks.SheafOfModules.CoproductSheafification.isLocallySurjective_toCoprod`: the canonical
  morphism from the objectwise coproduct is locally surjective.
* `Stacks.SheafOfModules.CoproductSheafification.exists_finset_eq_zero_of_ι`: **a section of
  `∐ M` over `V` is, on a covering sieve of `V`, supported in finitely many summands** — all
  but finitely many of its components vanish after restriction. The components are data,
  characterized by being the identity on their own summand and zero on the others, so a
  consumer passes the projections it already has;
  `Stacks.SheafOfModules.CoproductSheafification.exists_finset_proj_eq_zero` is the
  specialization to `proj`.
* `Stacks.SheafOfModules.CoproductSheafification.exists_finset_eq_zero_of_inj`: the
  module-theoretic input, that a point of the vertex of a colimiting cofan of modules is
  killed by all but finitely many components, with the same characterization of the
  components.

## Implementation notes

**Why the index type is `Type 0`.** The finiteness statement runs through `⨁ i, Z i`, whose
carrier lives in `Type (max w u)` for an index type in `Type w` and modules in `Type u`, and
which must therefore coincide with the vertex of the cofan, in `Type u`. So the index universe
has to be bounded by the module universe. Writing that bound in Mathlib's idiom — modules in
`ModuleCat.{max w t}`, as `ModuleCat.coprodIsoDirectSum` does — makes every declaration in the
sheaf half polymorphic in two universes that never occur apart, and the file's own internal
applications then require inverting `max`, which Lean will not do; the `checkUnivs` linter
flags the shape directly. Fixing the index at `Type 0` avoids the inversion entirely, because
`max 0 t` normalizes to `t`, and it is what the graded consumers have: the fibres of a
`ℤ`-graded tensor product are indexed by `{p : ℤ × ℤ // p.1 + p.2 = n}`, in `Type 0`. The
cost is real: a family indexed in the module universe — as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SiteFiniteTypeBridge.lean`, whose index types
are `Type w` for the module universe `w` — is *not* covered.

The identification `coprodIso` comes from the universal properties, exactly as in the free
case: the cocone on the sheafification of the objectwise coproduct whose legs are the
sheafified inclusions is colimiting because sheafification is a left adjoint, and the counit
of the sheafification adjunction identifies its vertices with the `M i`.

Finiteness enters only through `exists_finset_eq_zero_of_inj`, which is a statement about
modules and is proved by comparing the colimiting cofan with the direct sum: the support of
the corresponding element of `⨁ i, Z i` is the finite set asked for. The components are
described by the two equations characterizing them rather than by a biproduct, so no
finiteness of `I` is needed — and no lemma identifying one spelling of a projection with
another, which is why both finiteness statements quantify over the components.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Limits Opposite DirectSum

noncomputable section

namespace Stacks.SheafOfModules.CoproductSheafification

-- `shf` is the sheafification abbreviation of `FreeSheafification`; one copy only.
open FreeSheafification (shf)

universe v u u'

/-! ### The components of a coproduct of modules -/

section General

variable {D : Type*} [Category* D] [HasZeroMorphisms D] {I : Type*} [DecidableEq I] {Z : I → D}

/-- The `i`-th component of a colimiting cofan: the identity on the `i`-th summand and zero on
the others. -/
def cofanProj {c : Cofan Z} (hc : IsColimit c) (i : I) : c.pt ⟶ Z i :=
  Cofan.IsColimit.desc hc (fun j => if h : j = i then eqToHom (congrArg Z h) else 0)

/-- The `i`-th component kills every summand but the `i`-th, on which it is the identity. -/
theorem inj_cofanProj {c : Cofan Z} (hc : IsColimit c) (i j : I) :
    c.inj j ≫ cofanProj hc i = if h : j = i then eqToHom (congrArg Z h) else 0 :=
  Cofan.IsColimit.fac hc _ j

end General

section ModuleCat

variable {A : Type u} [Ring A] {I : Type v} [DecidableEq I] {Z : I → ModuleCat.{max v u'} A}

omit [DecidableEq I] in
/-- **A point of the vertex of a colimiting cofan of modules is killed by all but finitely many
components.** The components are not required to be any particular construction: any family
that is the identity on its own summand and zero on the others will do, which is how a consumer
supplies the components it already has. The finite set is the support of the corresponding
element of the direct sum. -/
theorem exists_finset_eq_zero_of_inj {c : Cofan Z} (hc : IsColimit c) (π : ∀ i, c.pt ⟶ Z i)
    (hself : ∀ i, c.inj i ≫ π i = 𝟙 (Z i))
    (hzero : ∀ i j, j ≠ i → c.inj j ≫ π i = 0) (t : c.pt) :
    ∃ S : Finset I, ∀ i ∉ S, (π i).hom t = 0 := by
  classical
  let e : c.pt ≅ ModuleCat.of A (⨁ i, Z i) :=
    hc.coconePointUniqueUpToIso (ModuleCat.coproductCoconeIsColimit Z)
  refine ⟨(e.hom.hom t).support, fun i hi => ?_⟩
  have key : π i = e.hom ≫ ModuleCat.ofHom (DirectSum.component A I (fun i => Z i) i) := by
    refine Cofan.IsColimit.hom_ext hc _ _ fun j => ?_
    rw [← Category.assoc,
      show c.inj j ≫ e.hom = ModuleCat.ofHom (DirectSum.lof A I (fun i => Z i) j) from
        hc.comp_coconePointUniqueUpToIso_hom (ModuleCat.coproductCoconeIsColimit Z) ⟨j⟩]
    by_cases h : j = i
    · subst h
      rw [hself]
      ext (b : Z j)
      simp
    · rw [hzero i j h]
      ext (b : Z j)
      simpa [h] using
        (DirectSum.component.of (R := A) (M := fun k => (Z k : Type _)) i j b).symm
  rw [key]
  exact DFinsupp.notMem_support_iff.1 hi

/-- `exists_finset_eq_zero_of_inj` for the components `cofanProj`. -/
theorem exists_finset_cofanProj_eq_zero {c : Cofan Z} (hc : IsColimit c) (t : c.pt) :
    ∃ S : Finset I, ∀ i ∉ S, (cofanProj hc i).hom t = 0 :=
  exists_finset_eq_zero_of_inj hc (cofanProj hc)
    (fun i => by rw [inj_cofanProj]; simp)
    (fun i j h => by rw [inj_cofanProj]; simp [h]) t

end ModuleCat

/-! ### Coproducts of sheaves of modules -/

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {I : Type} (M : I → SheafOfModules.{u} R) [HasCoproduct M]

/-- The coproduct of the underlying presheaves of modules. Unlike the coproduct in sheaves of
modules, this one is computed objectwise. -/
noncomputable abbrev presCoprod : PresheafOfModules.{u} R.obj := ∐ (fun i => (M i).val)

/-- The canonical morphism from the objectwise coproduct to the presheaf underlying `∐ M`,
given on the `i`-th summand by the `i`-th inclusion. -/
noncomputable def toCoprod : presCoprod R M ⟶ (∐ M).val :=
  Sigma.desc (fun i => (Sigma.ι M i).val)

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The `i`-th inclusion into the objectwise coproduct, followed by `toCoprod`, is the morphism
of presheaves underlying the `i`-th inclusion into `∐ M`. -/
@[reassoc (attr := simp)]
lemma ι_toCoprod (i : I) :
    Sigma.ι (fun i => (M i).val) i ≫ toCoprod R M = (Sigma.ι M i).val :=
  Sigma.ι_comp_desc _ _

/-- The sheafification of the presheaf underlying a sheaf of modules is that sheaf. -/
noncomputable abbrev valIso (N : SheafOfModules.{u} R) : (shf R).obj N.val ≅ N :=
  asIso (EpiMono.counitApp N)

/-- The morphism from the sheafification of the objectwise coproduct to `∐ M`. -/
noncomputable def coprodCompare : (shf R).obj (presCoprod R M) ⟶ ∐ M :=
  (shf R).map (toCoprod R M) ≫ EpiMono.counitApp (∐ M)

/-- The sheafified `i`-th inclusion, followed by `coprodCompare`, is `valIso` followed by the
`i`-th inclusion into `∐ M`. -/
lemma map_ι_coprodCompare (i : I) :
    (shf R).map (Sigma.ι (fun i => (M i).val) i) ≫ coprodCompare R M =
      (valIso R (M i)).hom ≫ Sigma.ι M i := by
  rw [show coprodCompare R M = (shf R).map (toCoprod R M) ≫ EpiMono.counitApp (∐ M) from rfl,
    ← Functor.map_comp_assoc, ι_toCoprod]
  exact EpiMono.counitApp_naturality (Sigma.ι M i)

/-- The inverse of `coprodCompare`, from the universal property of `∐ M`. -/
noncomputable def coprodCompareInv : (∐ M) ⟶ (shf R).obj (presCoprod R M) :=
  Sigma.desc (fun i => (valIso R (M i)).inv ≫
    (shf R).map (Sigma.ι (fun i => (M i).val) i))

/-- The `i`-th inclusion into `∐ M`, followed by `coprodCompareInv`, is the inverse of `valIso`
followed by the sheafified `i`-th inclusion. -/
@[reassoc]
lemma ι_coprodCompareInv (i : I) :
    Sigma.ι M i ≫ coprodCompareInv R M =
      (valIso R (M i)).inv ≫ (shf R).map (Sigma.ι (fun i => (M i).val) i) :=
  Sigma.ι_comp_desc _ _

/-- `coprodCompare` is an isomorphism: both source and target are colimiting cocone points for
the family `M`, the source because sheafification is a left adjoint. -/
instance isIso_coprodCompare : IsIso (coprodCompare R M) := by
  refine ⟨coprodCompareInv R M, ?_, ?_⟩
  · refine Cofan.IsColimit.hom_ext
      (isColimitOfHasCoproductOfPreservesColimit (shf R) (fun i => (M i).val)) _ _ fun i => ?_
    rw [cofan_mk_inj, ← Category.assoc, map_ι_coprodCompare, Category.assoc,
      ι_coprodCompareInv, Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  · refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, ι_coprodCompareInv, Category.assoc, map_ι_coprodCompare,
      Iso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm

/-- **A coproduct of sheaves of modules is the sheafification of the coproduct of the
underlying presheaves of modules.** -/
noncomputable def coprodIso : (shf R).obj (presCoprod R M) ≅ ∐ M :=
  asIso (coprodCompare R M)

/-- Sheafifying `toCoprod` gives an isomorphism of sheaves of modules. -/
instance isIso_shf_map_toCoprod : IsIso ((shf R).map (toCoprod R M)) :=
  have : IsIso ((shf R).map (toCoprod R M) ≫ EpiMono.counitApp (∐ M)) := isIso_coprodCompare R M
  IsIso.of_isIso_comp_right _ (EpiMono.counitApp (∐ M))

/-- **The canonical morphism from the objectwise coproduct to `∐ M` is locally surjective.**
Every section of `∐ M` becomes, after restriction along the arrows of a covering sieve, a
section of the objectwise coproduct. -/
theorem isLocallySurjective_toCoprod :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (toCoprod R M)) := by
  have h2 : IsIso ((SheafOfModules.toSheaf R).map ((shf R).map (toCoprod R M))) := inferInstance
  have h3 : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf R.obj).map (toCoprod R M))) := h2
  exact (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J _).1
    (Sheaf.isLocallySurjective_of_iso _)

/-- **Section-level form.** The sieve of arrows along which a section of `∐ M` restricts to a
section of the objectwise coproduct is a covering sieve. -/
theorem imageSieve_toCoprod_mem {V : C}
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).obj (op V))) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map (toCoprod R M)) s ∈ J V :=
  have := isLocallySurjective_toCoprod R M
  Presheaf.imageSieve_mem J _ s

section Components

variable [DecidableEq I]

/-- The `i`-th component of `∐ M`, the identity on the `i`-th summand and zero on the others. -/
noncomputable def proj (i : I) : (∐ M) ⟶ M i :=
  cofanProj (coproductIsCoproduct M) i

/-- The `i`-th component of the objectwise coproduct. -/
noncomputable def presProj (i : I) : presCoprod R M ⟶ (M i).val :=
  cofanProj (coproductIsCoproduct (fun i => (M i).val)) i

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The `i`-th component of `∐ M` on the `j`-th summand. -/
theorem ι_proj (i j : I) :
    Sigma.ι M j ≫ proj R M i = if h : j = i then eqToHom (congrArg M h) else 0 :=
  inj_cofanProj (coproductIsCoproduct M) i j

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasCoproduct M] in
/-- The `i`-th component of the objectwise coproduct on the `j`-th summand. -/
theorem ι_presProj (i j : I) :
    Sigma.ι (fun i => (M i).val) j ≫ presProj R M i =
      if h : j = i then eqToHom (congrArg (fun k => (M k).val) h) else 0 :=
  inj_cofanProj (coproductIsCoproduct (fun i => (M i).val)) i j

omit [DecidableEq I] in
/-- **A section of a coproduct of sheaves of modules is locally supported in finitely many
summands.** On a covering sieve of `V`, every restriction of a section `s` of `∐ M` over `V` is
killed by all but finitely many of the components.

The components are given as data, characterized by the two equations the canonical ones
satisfy: a consumer passes the components it already has — for a graded tensor product,
`CategoryTheory.GradedObject.Monoidal.πTensorObj` together with
`ιTensorObj_πTensorObj_self` and `ιTensorObj_πTensorObj_ne` — so no identification of two
spellings of one projection is needed anywhere.

This is the statement that the coproduct, although formed by sheafification and therefore not
objectwise, is objectwise *after localization*: the finite set of summands depends on the
member of the covering, not only on `s`. -/
theorem exists_finset_eq_zero_of_ι {V : C} (π : ∀ i, (∐ M) ⟶ M i)
    (hself : ∀ i, Sigma.ι M i ≫ π i = 𝟙 (M i))
    (hzero : ∀ i j, j ≠ i → Sigma.ι M j ≫ π i = 0)
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).obj (op V))) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g → ∃ S : Finset I, ∀ i ∉ S,
      ((PresheafOfModules.toPresheaf R.obj).map (π i).val).app (op W)
        ((((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).map g.op) s) = 0 := by
  classical
  have key : ∀ i j, Sigma.ι (fun k => (M k).val) j ≫ toCoprod R M ≫ (π i).val =
      (Sigma.ι M j ≫ π i).val := fun i j => by rw [← Category.assoc, ι_toCoprod]; rfl
  refine ⟨_, imageSieve_toCoprod_mem R M s, fun {W} g hg => ?_⟩
  obtain ⟨t, ht⟩ := hg
  obtain ⟨S, hS⟩ := exists_finset_eq_zero_of_inj
    (isColimitOfHasCoproductOfPreservesColimit
      (PresheafOfModules.evaluation R.obj (op W)) (fun i => (M i).val))
    (fun i => (toCoprod R M ≫ (π i).val).app (op W))
    (fun i => by
      exact congrArg (fun f : (M i).val ⟶ (M i).val => f.app (op W))
        ((key i i).trans (congrArg _ (hself i))))
    (fun i j h => by
      exact congrArg (fun f : (M j).val ⟶ (M i).val => f.app (op W))
        ((key i j).trans (congrArg _ (hzero i j h))))
    (t : ((presCoprod R M).obj (op W) : ModuleCat _))
  refine ⟨S, fun i hi => ?_⟩
  rw [← ht]
  exact hS i hi

/-- `exists_finset_eq_zero_of_ι` for the components `proj`. -/
theorem exists_finset_proj_eq_zero {V : C}
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).obj (op V))) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g → ∃ S : Finset I, ∀ i ∉ S,
      ((PresheafOfModules.toPresheaf R.obj).map (proj R M i).val).app (op W)
        ((((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).map g.op) s) = 0 :=
  exists_finset_eq_zero_of_ι R M (proj R M)
    (fun i => by rw [ι_proj]; simp)
    (fun i j h => by rw [ι_proj]; simp [h]) s

end Components

end Stacks.SheafOfModules.CoproductSheafification

end

end
