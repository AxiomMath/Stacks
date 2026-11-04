module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductLocalFiniteSum

/-!
# Local finite sums in a coproduct of sheaves of modules indexed in the module universe

`Stacks.SheafOfModules.CoproductSheafification.exists_sieve_sum_inj_of_isColimit` says that a
section of the vertex of a colimiting cofan of sheaves of modules is, on a covering sieve, a
finite sum of sections of the summands, for an index type in `Type`. This file proves the same
statement for an index type in the universe of the module sections, which is the generality of
the direct sums `⊕ᵢ j_{Uᵢ!} O_{Uᵢ}` that resolve sheaves of modules.

## Main results

* `Stacks.SheafOfModules.CoproductSheafificationLarge.exists_sieve_sum_inj_of_isColimit`: a
  section of the vertex of a colimiting cofan is, on a covering sieve, a finite sum of sections
  of the summands.
-/

@[expose] public section

open CategoryTheory Limits Opposite DirectSum

noncomputable section

namespace Stacks.SheafOfModules.CoproductSheafificationLarge

open FreeSheafification (shf)
open Stacks.SheafOfModules.CoproductSheafification (exists_finset_sum_inj_of_isColimit)

universe v u u'

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The coproduct of the underlying presheaves of modules. Unlike the coproduct in sheaves of
modules, this one is computed objectwise. -/
noncomputable abbrev presCoprod
    {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] :
    PresheafOfModules.{u} R.obj := ∐ (fun i => (M i).val)

/-- The canonical morphism from the objectwise coproduct to the presheaf underlying `∐ M`,
given on the `i`-th summand by the `i`-th inclusion. -/
noncomputable def toCoprod
    {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] : presCoprod R M ⟶ (∐ M).val :=
  Sigma.desc (fun i => (Sigma.ι M i).val)

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The `i`-th inclusion into the objectwise coproduct followed by `toCoprod` is the underlying
morphism of presheaves of the `i`-th inclusion into `∐ M`. -/
@[reassoc (attr := simp)]
lemma ι_toCoprod {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] (i : I) :
    Sigma.ι (fun i => (M i).val) i ≫ toCoprod R M = (Sigma.ι M i).val :=
  Sigma.ι_desc _ _

/-- The morphism from the sheafification of the objectwise coproduct to `∐ M`. -/
noncomputable def coprodCompare
    {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] :
    (shf R).obj (presCoprod R M) ⟶ ∐ M :=
  (shf R).map (toCoprod R M) ≫ EpiMono.counitApp (∐ M)

/-- The sheafified `i`-th inclusion followed by `coprodCompare` is, up to the isomorphism
`valIso` from the sheafification of `(M i).val` to `M i`, the `i`-th inclusion into `∐ M`. -/
lemma map_ι_coprodCompare {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] (i : I) :
    (shf R).map (Sigma.ι (fun i => (M i).val) i) ≫ coprodCompare R M =
      (Stacks.SheafOfModules.CoproductSheafification.valIso R (M i)).hom ≫ Sigma.ι M i := by
  rw [show coprodCompare R M = (shf R).map (toCoprod R M) ≫ EpiMono.counitApp (∐ M) from rfl,
    ← Functor.map_comp_assoc, ι_toCoprod]
  exact EpiMono.counitApp_naturality (Sigma.ι M i)

/-- The inverse of `coprodCompare`, from the universal property of `∐ M`. -/
noncomputable def coprodCompareInv
    {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] :
    (∐ M) ⟶ (shf R).obj (presCoprod R M) :=
  Sigma.desc (fun i => (Stacks.SheafOfModules.CoproductSheafification.valIso R (M i)).inv ≫
    (shf R).map (Sigma.ι (fun i => (M i).val) i))

/-- The `i`-th inclusion into `∐ M` followed by `coprodCompareInv` is the inverse of `valIso`
followed by the sheafified `i`-th inclusion into the objectwise coproduct. -/
@[reassoc]
lemma ι_coprodCompareInv {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] (i : I) :
    Sigma.ι M i ≫ coprodCompareInv R M =
      (Stacks.SheafOfModules.CoproductSheafification.valIso R (M i)).inv ≫
        (shf R).map (Sigma.ι (fun i => (M i).val) i) :=
  Sigma.ι_desc _ _

/-- `coprodCompare` is an isomorphism: both source and target are colimiting cocone points for
the family `M`, the source because sheafification is a left adjoint. -/
instance isIso_coprodCompare
    {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] : IsIso (coprodCompare R M) := by
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
noncomputable def coprodIso
    {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] :
    (shf R).obj (presCoprod R M) ≅ ∐ M :=
  asIso (coprodCompare R M)

/-- Sheafifying `toCoprod` gives an isomorphism of sheaves of modules. -/
instance isIso_shf_map_toCoprod
    {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] :
    IsIso ((shf R).map (toCoprod R M)) :=
  have : IsIso ((shf R).map (toCoprod R M) ≫ EpiMono.counitApp (∐ M)) := isIso_coprodCompare R M
  IsIso.of_isIso_comp_right _ (EpiMono.counitApp (∐ M))

/-- **The canonical morphism from the objectwise coproduct to `∐ M` is locally surjective.**
Every section of `∐ M` becomes, after restriction along the arrows of a covering sieve, a
section of the objectwise coproduct. -/
theorem isLocallySurjective_toCoprod {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (toCoprod R M)) := by
  have h2 : IsIso ((SheafOfModules.toSheaf R).map ((shf R).map (toCoprod R M))) := inferInstance
  have h3 : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf R.obj).map (toCoprod R M))) := h2
  exact (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J _).1
    (Sheaf.isLocallySurjective_of_iso _)

/-- The sieve of arrows along which a section of `∐ M` restricts to a section of the objectwise
coproduct is a covering sieve. -/
theorem imageSieve_toCoprod_mem {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] {V : C}
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).obj (op V))) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map (toCoprod R M)) s ∈ J V :=
  have := isLocallySurjective_toCoprod R M
  Presheaf.imageSieve_mem J _ s

/-- Every section `s` of `∐ M` over `V` is, after restriction along each arrow of some covering
sieve on `V`, a finite sum of images of sections of the summands `M i` under the inclusions. -/
theorem exists_sieve_sum_ι {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M] {V : C}
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).obj (op V))) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
      ∃ (S : Finset I)
        (y : ∀ i : I,
          ToType (((PresheafOfModules.toPresheaf R.obj).obj (M i).val).obj (op W))),
        (((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).map g.op) s =
          ∑ i ∈ S,
            ((PresheafOfModules.toPresheaf R.obj).map (Sigma.ι M i).val).app (op W) (y i) := by
  classical
  refine ⟨_, imageSieve_toCoprod_mem R M s, fun {W} g hg => ?_⟩
  obtain ⟨t, ht⟩ := hg
  obtain ⟨S, y, hy⟩ := exists_finset_sum_inj_of_isColimit
    (isColimitOfHasCoproductOfPreservesColimit
      (PresheafOfModules.evaluation R.obj (op W)) (fun i => (M i).val))
    (t : ((presCoprod R M).obj (op W) : ModuleCat _))
  refine ⟨S, y, ?_⟩
  rw [← ht]
  have hsum : (t : ((presCoprod R M).obj (op W) : ModuleCat _)) =
      ∑ i ∈ S, ((Sigma.ι (fun k => (M k).val) i).app (op W)).hom (y i) := hy
  rw [show ((PresheafOfModules.toPresheaf R.obj).map (toCoprod R M)).app (op W) t =
      ((toCoprod R M).app (op W)).hom (t : ((presCoprod R M).obj (op W) : ModuleCat _)) from rfl,
    hsum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun f : (M i).val.obj (op W) ⟶ (∐ M).val.obj (op W) => f.hom (y i))
    (congrArg (fun f : (M i).val ⟶ (∐ M).val => f.app (op W)) (ι_toCoprod R M i))

/-- **Local finite sums in a coproduct.** For a colimiting cofan `c` of a family `M` of sheaves of
modules indexed by `I : Type u`, every section `s` of `c.pt` over `V` is, after restriction along
each arrow `g : W ⟶ V` of some covering sieve, a finite sum `∑ i ∈ S, c.inj i (y i)` of images
of sections `y i` of the summands. -/
theorem exists_sieve_sum_inj_of_isColimit
    {I : Type u} (M : I → SheafOfModules.{u} R) [HasCoproduct M]
    {c : Cofan M} (hc : IsColimit c) {V : C}
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj c.pt.val).obj (op V))) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), T g →
      ∃ (S : Finset I)
        (y : ∀ i : I,
          ToType (((PresheafOfModules.toPresheaf R.obj).obj (M i).val).obj (op W))),
        (((PresheafOfModules.toPresheaf R.obj).obj c.pt.val).map g.op) s =
          ∑ i ∈ S,
            ((PresheafOfModules.toPresheaf R.obj).map (c.inj i).val).app (op W) (y i) := by
  classical
  let e : (∐ M) ≅ c.pt := (coproductIsCoproduct M).coconePointUniqueUpToIso hc
  have hι : ∀ i : I, Sigma.ι M i ≫ e.hom = c.inj i := fun i =>
    (coproductIsCoproduct M).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  obtain ⟨T, hT, hsum⟩ := exists_sieve_sum_ι R M
    (((PresheafOfModules.toPresheaf R.obj).map e.inv.val).app (op V) s)
  refine ⟨T, hT, fun {W} g hg => ?_⟩
  obtain ⟨S, y, hy⟩ := hsum g hg
  refine ⟨S, y, ?_⟩
  have hnat := congrArg (fun z => ((PresheafOfModules.toPresheaf R.obj).map e.hom.val).app
    (op W) z) hy
  simp only [map_sum] at hnat
  have hcancel : ((PresheafOfModules.toPresheaf R.obj).map e.hom.val).app (op V)
      (((PresheafOfModules.toPresheaf R.obj).map e.inv.val).app (op V) s) = s := by
    have hid : e.inv.val ≫ e.hom.val = 𝟙 _ := congrArg SheafOfModules.Hom.val e.inv_hom_id
    rw [← CategoryTheory.comp_apply, ← NatTrans.comp_app, ← Functor.map_comp, hid,
      CategoryTheory.Functor.map_id, NatTrans.id_app, CategoryTheory.id_apply]
  have hnatur : ((PresheafOfModules.toPresheaf R.obj).map e.hom.val).app (op W)
        ((((PresheafOfModules.toPresheaf R.obj).obj (∐ M).val).map g.op)
          (((PresheafOfModules.toPresheaf R.obj).map e.inv.val).app (op V) s)) =
      (((PresheafOfModules.toPresheaf R.obj).obj c.pt.val).map g.op) s := by
    have h := ConcreteCategory.congr_hom
      (((PresheafOfModules.toPresheaf R.obj).map e.hom.val).naturality g.op)
      (((PresheafOfModules.toPresheaf R.obj).map e.inv.val).app (op V) s)
    simp only [CategoryTheory.comp_apply] at h
    rw [h, hcancel]
  exact hnatur.symm.trans (hnat.trans (Finset.sum_congr rfl fun i _ =>
    congrArg (fun f : (M i).val ⟶ c.pt.val =>
        ((PresheafOfModules.toPresheaf R.obj).map f).app (op W) (y i))
      (congrArg SheafOfModules.Hom.val (hι i))))

end Stacks.SheafOfModules.CoproductSheafificationLarge
