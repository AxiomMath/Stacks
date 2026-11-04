module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusKernelConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechFrobeniusMatrix
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The free module of rank `r` on the small étale site of Stacks 021B, with a Frobenius matrix

Let `B` be a big étale site and `S` a scheme of `B`. The sheaf of modules `V ↦ Γ(V)^r` over the
structure sheaf of the small étale site of `S` of Stacks 021B is finite locally free, being
isomorphic to the free module on `r` generators. A matrix `a` of global functions defines the
`p`-semilinear endomorphism `b ↦ (∑ᵢ aᵢⱼ bᵢ ^ p)ⱼ` of its underlying abelian sheaf, so
[Stacks, Tag 0GKU] applies to it.

## Main definitions

* `Stacks.ArtinSchreier.smallFreeModule`: `V ↦ Γ(V)^r`.
* `Stacks.ArtinSchreier.smallFreeModuleIso`: its identification with the free module.
* `Stacks.ArtinSchreier.smallFrobMatrix`: the Frobenius endomorphism given by a matrix.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.ArtinSchreier

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (r : ℕ)

/-- The ring of functions on an object of the small étale site of Stacks 021B. -/
abbrev smallRing (V : (SmallEtale B S hS)ᵒᵖ) : Type u :=
  (SmallEtale.structureSheaf B S hS).obj.obj V

/-- `V ↦ Γ(V)^r` on the small étale site of Stacks 021B, as an abelian presheaf. -/
def smallFreePresheaf : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (Fin r → smallRing B S hS V)
  map g := AddCommGrpCat.ofHom
    { toFun := fun b i => ((SmallEtale.structureSheaf B S hS).obj.map g).hom (b i)
      map_zero' := funext fun _ => map_zero _
      map_add' := fun _ _ => funext fun _ => map_add _ _ _ }
  map_id V := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b => funext fun i => ?_)
    change ((SmallEtale.structureSheaf B S hS).obj.map (𝟙 V)).hom (b i) = b i
    rw [(SmallEtale.structureSheaf B S hS).obj.map_id]
    rfl
  map_comp g h := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b => funext fun i => ?_)
    change ((SmallEtale.structureSheaf B S hS).obj.map (g ≫ h)).hom (b i) =
      ((SmallEtale.structureSheaf B S hS).obj.map h).hom
        (((SmallEtale.structureSheaf B S hS).obj.map g).hom (b i))
    rw [(SmallEtale.structureSheaf B S hS).obj.map_comp]
    rfl

/-- The sections `Γ(V)^r` of `smallFreePresheaf` form a module over `Γ(V)`. -/
instance (V : (SmallEtale B S hS)ᵒᵖ) :
    Module ((SmallEtale.structureSheaf B S hS).obj.obj V) ((smallFreePresheaf B S hS r).obj V) :=
  inferInstanceAs (Module _ (Fin r → smallRing B S hS V))

/-- `V ↦ Γ(V)^r` satisfies the sheaf condition for the topology of the small étale site of
Stacks 021B, as a presheaf of types. -/
theorem isSheaf_forget_smallFreePresheaf :
    Presieve.IsSheaf (SmallEtale.topology B S hS)
      (smallFreePresheaf B S hS r ⋙ CategoryTheory.forget AddCommGrpCat) := by
  intro U R hR x hx
  have hG := SmallEtale.isSheaf_globalSections B S hS R hR
  let xi : Fin r → Presieve.FamilyOfElements
      ((SmallEtale.toScheme B S hS).op ⋙ Stacks.Sites.globalSectionsSheaf.obj) R :=
    fun i _ g hg => (show Fin r → smallRing B S hS _ from x g hg) i
  have hxi : ∀ i, (xi i).Compatible := fun i Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w =>
    congrFun (hx g₁ g₂ h₁ h₂ w) i
  exact ⟨fun i => hG.amalgamate (xi i) (hxi i),
    fun Y g hg => funext fun i => hG.isAmalgamation (hxi i) g hg,
    fun t' ht' => funext fun i => hG.isSeparatedFor (xi i) (t' i) (hG.amalgamate (xi i) (hxi i))
      (fun Y g hg => congrFun (ht' g hg) i) (hG.isAmalgamation (hxi i))⟩

/-- **`V ↦ Γ(V)^r` as a sheaf of modules over the structure sheaf.** -/
def smallFreeModule : SheafOfModules.{u} (SmallEtale.structureSheaf B S hS) where
  val := PresheafOfModules.ofPresheaf (smallFreePresheaf B S hS r) (fun _ _ g c b => funext
    fun i => map_mul ((SmallEtale.structureSheaf B S hS).obj.map g).hom c (b i))
  isSheaf := Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget _ _
    (isSheaf_forget_smallFreePresheaf B S hS r)

variable {B S hS r}

/-- A finite sum of morphisms of sheaves of modules is computed on sections. -/
theorem sheafOfModules_sum_val_app {R : Sheaf (SmallEtale.topology B S hS) RingCat.{u}}
    {M N : SheafOfModules.{u} R} {κ : Type*} (s : Finset κ) (f : κ → (M ⟶ N))
    (V : (SmallEtale B S hS)ᵒᵖ) (m : M.val.obj V) :
    (∑ i ∈ s, f i).val.app V m = ∑ i ∈ s, (f i).val.app V m := by
  show ((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj V).map
    (∑ i ∈ s, f i)).hom m = _
  rw [Functor.map_sum, ModuleCat.hom_sum]
  exact LinearMap.sum_apply s _ m

/-- The `i`-th coordinate `Γ(V)^r ⟶ Γ(V)`. -/
def smallFreeProj (i : Fin r) :
    smallFreeModule B S hS r ⟶ SheafOfModules.unit (SmallEtale.structureSheaf B S hS) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun _ => smallRing B S hS V) i)
      naturality _ _ _ := rfl }
    (fun _ _ _ => rfl)⟩

/-- `smallFreeProj i` takes the `i`-th coordinate of a section of `Γ(V)^r`. -/
theorem smallFreeProj_app (i : Fin r) (V : (SmallEtale B S hS)ᵒᵖ)
    (b : (smallFreeModule B S hS r).val.obj V) :
    (smallFreeProj i).val.app V b = (show Fin r → smallRing B S hS V from b) i :=
  rfl

/-- The `i`-th standard section of `Γ(V)^r`. -/
def smallFreeSection (i : Fin r) : (smallFreeModule B S hS r).sections :=
  PresheafOfModules.sectionsMk
    (fun V => (Pi.single (M := fun _ : Fin r => smallRing B S hS V) i 1))
    (fun V W g => funext fun j => by
      change ((SmallEtale.structureSheaf B S hS).obj.map g).hom
          (Pi.single (M := fun _ : Fin r => smallRing B S hS V) i 1 j) =
        Pi.single (M := fun _ : Fin r => smallRing B S hS W) i 1 j
      by_cases h : j = i
      · subst h
        rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero])

/-- The value of `smallFreeSection i` on `V` is the `i`-th standard basis vector of `Γ(V)^r`. -/
theorem smallFreeSection_val (i : Fin r) (V : (SmallEtale B S hS)ᵒᵖ) :
    (smallFreeSection (B := B) (hS := hS) i).val V =
      (Pi.single (M := fun _ : Fin r => smallRing B S hS V) i 1) :=
  rfl

/-- The comparison `free r ⟶ Γ(-)^r` sending the generators to the standard sections. -/
def smallFreeFromFree :
    SheafOfModules.free (R := SmallEtale.structureSheaf B S hS) (ULift.{u} (Fin r)) ⟶
      smallFreeModule B S hS r :=
  (smallFreeModule B S hS r).freeHomEquiv.symm fun i => smallFreeSection i.down

/-- The comparison `Γ(-)^r ⟶ free r`. -/
def smallFreeToFree :
    smallFreeModule B S hS r ⟶
      SheafOfModules.free (R := SmallEtale.structureSheaf B S hS) (ULift.{u} (Fin r)) :=
  ∑ i : Fin r, smallFreeProj i ≫ SheafOfModules.ιFree (ULift.up i)

/-- `smallFreeFromFree` sends the `j`-th generator of the free module to the `j`-th standard
section. -/
theorem ιFree_smallFreeFromFree (j : ULift.{u} (Fin r)) :
    SheafOfModules.ιFree j ≫ smallFreeFromFree (B := B) (hS := hS) (r := r) =
      (smallFreeModule B S hS r).unitHomEquiv.symm (smallFreeSection j.down) := by
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, smallFreeFromFree,
    Equiv.apply_symm_apply]

/-- The `i`-th coordinate of the morphism from the unit given by the `j`-th standard section is
the identity if `i = j` and zero otherwise. -/
theorem unitHomEquiv_symm_comp_smallFreeProj (i j : Fin r) :
    (smallFreeModule B S hS r).unitHomEquiv.symm (smallFreeSection j) ≫ smallFreeProj i =
      if i = j then 𝟙 _ else 0 := by
  apply (SheafOfModules.unitHomEquiv _).injective
  rw [SheafOfModules.unitHomEquiv_symm_comp, Equiv.apply_symm_apply]
  refine PresheafOfModules.sections_ext _ _ fun V => ?_
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    show (Pi.single (M := fun _ : Fin r => smallRing B S hS V) i 1) i = (1 : smallRing B S hS V)
    rw [Pi.single_eq_same]
  · rw [if_neg h]
    show (Pi.single j 1 : Fin r → smallRing B S hS V) i = (0 : smallRing B S hS V)
    rw [Pi.single_eq_of_ne h]

/-- `smallFreeFromFree` followed by `smallFreeToFree` is the identity of the free module. -/
theorem smallFreeFromFree_comp_toFree :
    smallFreeFromFree (B := B) (hS := hS) (r := r) ≫ smallFreeToFree = 𝟙 _ := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan _) _ _ fun j => ?_
  show SheafOfModules.ιFree j ≫ _ = SheafOfModules.ιFree j ≫ _
  rw [← Category.assoc, ιFree_smallFreeFromFree, smallFreeToFree, Preadditive.comp_sum,
    Category.comp_id]
  simp only [← Category.assoc, unitHomEquiv_symm_comp_smallFreeProj]
  rw [Finset.sum_eq_single j.down (fun i _ hi => by rw [if_neg hi, zero_comp])
    (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, Category.id_comp]

/-- `smallFreeToFree` followed by `smallFreeFromFree` is the identity of `Γ(-)^r`. -/
theorem smallFreeToFree_comp_fromFree :
    smallFreeToFree ≫ smallFreeFromFree (B := B) (hS := hS) (r := r) = 𝟙 _ := by
  rw [smallFreeToFree, Preadditive.sum_comp]
  simp only [Category.assoc, ιFree_smallFreeFromFree]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun b => ?_))
  show (∑ i : Fin r, smallFreeProj i ≫ (smallFreeModule B S hS r).unitHomEquiv.symm
    (smallFreeSection i)).val.app V b = b
  rw [sheafOfModules_sum_val_app]
  show (∑ i : Fin r, (show Fin r → smallRing B S hS V from b) i •
      (Pi.single (M := fun _ : Fin r => smallRing B S hS V) i 1) : Fin r → smallRing B S hS V) =
    (show Fin r → smallRing B S hS V from b)
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  exact (Finset.sum_ite_eq Finset.univ j _).trans (if_pos (Finset.mem_univ j))

/-- **`Γ(-)^r` is the free module on `r` generators.** -/
def smallFreeModuleIso :
    SheafOfModules.free (R := SmallEtale.structureSheaf B S hS) (ULift.{u} (Fin r)) ≅
      smallFreeModule B S hS r where
  hom := smallFreeFromFree
  inv := smallFreeToFree
  hom_inv_id := smallFreeFromFree_comp_toFree
  inv_hom_id := smallFreeToFree_comp_fromFree

/-- `Γ(-)^r` is finite locally free. -/
instance isFiniteLocallyFree_smallFreeModule :
    SheafOfModules.IsFiniteLocallyFree (smallFreeModule B S hS r) :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r
    (hM := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso smallFreeModuleIso
      (SheafOfModules.isFiniteLocallyFreeOfRank_free r))

section Frobenius

variable (B S hS r) {p : ℕ} (hp : p.Prime) (hpS : (p : Γ(S, ⊤)) = 0) (a : Fin r → Fin r → Γ(S, ⊤))

/-- The object of Mathlib's small étale site underlying an object of the small étale site of
Stacks 021B. -/
abbrev toEtale {B S hS} (V : (SmallEtale B S hS)ᵒᵖ) : S.Etale :=
  (SmallEtale.toEtaleSite B S hS).obj V.unop

include hp hpS in
/-- **The Frobenius of `Γ(-)^r` given by a matrix**, `b ↦ (∑ᵢ aᵢⱼ bᵢ ^ p)ⱼ`, on the small étale
site of Stacks 021B. -/
def smallFrobMatrix :
    (SheafOfModules.toSheaf _).obj (smallFreeModule B S hS r) ⟶
      (SheafOfModules.toSheaf _).obj (smallFreeModule B S hS r) :=
  ⟨{ app V := AddCommGrpCat.ofHom
       { toFun := fun b => (show Fin r → smallRing B S hS V from
           frobMatrixFun S a p (toEtale V) (show Fin r → Γ((toEtale V).left, ⊤) from b))
         map_zero' := funext fun j => by
           change ∑ i, etaleFunction (toEtale V) (a i j) * (0 : Γ((toEtale V).left, ⊤)) ^ p = 0
           exact Finset.sum_eq_zero fun i _ => by rw [zero_pow hp.ne_zero, mul_zero]
         map_add' := fun b b' => frobMatrixFun_add S hp hpS a (toEtale V) b b' }
     naturality V₁ V₂ g := by
       refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b => funext fun j => ?_)
       let g' : toEtale V₂ ⟶ toEtale V₁ := (SmallEtale.toEtaleSite B S hS).map g.unop
       change ∑ i, etaleFunction (toEtale V₂) (a i j) * (g'.left.appTop.hom
           ((show Fin r → Γ((toEtale V₁).left, ⊤) from b) i)) ^ p =
         g'.left.appTop.hom (∑ i, etaleFunction (toEtale V₁) (a i j) *
           (show Fin r → Γ((toEtale V₁).left, ⊤) from b) i ^ p)
       rw [map_sum]
       refine Finset.sum_congr rfl fun i _ => ?_
       rw [map_mul, map_pow, appTop_etaleFunction] }⟩

/-- On sections over `V`, `smallFrobMatrix` is `frobMatrixFun`, `b ↦ (∑ᵢ aᵢⱼ bᵢ ^ p)ⱼ`. -/
theorem smallFrobMatrix_app (V : (SmallEtale B S hS)ᵒᵖ)
    (b : (smallFreeModule B S hS r).val.obj V) :
    SheafOfModules.sectionsAddHom (smallFrobMatrix B S hS r hp hpS a) V b =
      (show Fin r → smallRing B S hS V from
        frobMatrixFun S a p (toEtale V) (show Fin r → Γ((toEtale V).left, ⊤) from b)) :=
  rfl

/-- The Frobenius matrix map is `p`-semilinear. -/
theorem smallFrobMatrix_smul (U : SmallEtale B S hS)
    (c : (SmallEtale.structureSheaf B S hS).obj.obj (op U))
    (e : (smallFreeModule B S hS r).val.obj (op U)) :
    SheafOfModules.sectionsAddHom (smallFrobMatrix B S hS r hp hpS a) (op U) (c • e) =
      c ^ p • SheafOfModules.sectionsAddHom (smallFrobMatrix B S hS r hp hpS a) (op U) e := by
  rw [smallFrobMatrix_app, smallFrobMatrix_app]
  funext j
  show ∑ i, etaleFunction (toEtale (op U)) (a i j) *
      ((show Γ((toEtale (op U)).left, ⊤) from c) *
        (show Fin r → Γ((toEtale (op U)).left, ⊤) from e) i) ^ p =
    (show Γ((toEtale (op U)).left, ⊤) from c) ^ p * ∑ i, etaleFunction (toEtale (op U)) (a i j) *
      (show Fin r → Γ((toEtale (op U)).left, ⊤) from e) i ^ p
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow]
  ring

/-- **[Stacks, Tag 0GKU] for `Γ(-)^r` and a Frobenius matrix**, on the small étale site of
Stacks 021B. -/
theorem smallFrobMatrix_zeroGKU [Fact p.Prime] :
    IsZero (cokernel (smallFrobMatrix B S hS r hp hpS a - 𝟙 _)) ∧
      IsConstructibleAbelianSheaf B (B.obj S hS)
        ((sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (kernel (smallFrobMatrix B S hS r hp hpS a - 𝟙 _))) :=
  isZero_cokernel_and_isConstructible_kernel_frobeniusSemilinear_sub_id B p S hS
    (smallFreeModule B S hS r) hpS (smallFrobMatrix B S hS r hp hpS a)
    (smallFrobMatrix_smul B S hS r hp hpS a)

end Frobenius

section Transport

variable (B S hS r) {p : ℕ} (hp : p.Prime) (hpS : (p : Γ(S, ⊤)) = 0)
  (a : Fin r → Fin r → Γ(S, ⊤))

/-- **`𝐆_a^r` read on the small étale site of Stacks 021B is `Γ(-)^r`**, with the universe of
its sections raised. -/
def freeAdditiveSheafRestrictIso :
    (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.obj (freeAdditiveSheaf S r) ≅
      (sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((SheafOfModules.toSheaf _).obj (smallFreeModule B S hS r)) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun V => AddEquiv.toAddCommGrpIso
      { toFun := fun b => ULift.up (show Fin r → smallRing B S hS V from b.down)
        invFun := fun b => ULift.up (show Fin r → Γ((toEtale V).left, ⊤) from b.down)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }) (fun _ => rfl))

include hp hpS in
/-- Under `freeAdditiveSheafRestrictIso`, the Frobenius matrix map minus the identity of `𝐆_a^r`
is that of `Γ(-)^r`. -/
theorem freeAdditiveSheafRestrictIso_hom_comm :
    (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.map
        (frobMatrixMap S hp hpS a - 𝟙 _) ≫ (freeAdditiveSheafRestrictIso B S hS r).hom =
      (freeAdditiveSheafRestrictIso B S hS r).hom ≫
        (sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          (smallFrobMatrix B S hS r hp hpS a - 𝟙 _) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b => rfl)

/-- Raising the universe of the sections of abelian sheaves on the small étale site of
Stacks 021B preserves finite limits. -/
theorem preservesFiniteLimits_sheafCompose_uliftFunctor :
    PreservesFiniteLimits
      (sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}) := by
  let F := sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}
  let G := sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}
  let : PreservesFiniteLimits (F ⋙ G) := by
    show PreservesFiniteLimits (sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u + 1, u})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves F G

/-- Raising the universe of the sections preserves local surjectivity. -/
theorem isLocallySurjective_sheafCompose_uliftFunctor
    {F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u}} (φ : F ⟶ G)
    [Sheaf.IsLocallySurjective φ] :
    Sheaf.IsLocallySurjective
      ((sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).map φ) :=
  ⟨fun {U} s => (SmallEtale.topology B S hS).superset_covering
    (fun V g hg => by
      obtain ⟨t, ht⟩ := hg
      exact ⟨ULift.up t, ULift.ext _ _ ht⟩)
    (Presheaf.imageSieve_mem (SmallEtale.topology B S hS) φ.hom s.down)⟩

include B hS hp hpS in
/-- **The Frobenius matrix map minus the identity of `𝐆_a^r` is an epimorphism**, by
[Stacks, Tag 0GKU]. -/
@[sga "1 XI 6.7" "more general"]
theorem epi_frobMatrixMap_sub_id [Fact p.Prime] : Epi (frobMatrixMap S hp hpS a - 𝟙 _) := by
  have h1 : Epi (smallFrobMatrix B S hS r hp hpS a - 𝟙 _) :=
    Preadditive.epi_of_isZero_cokernel _ (smallFrobMatrix_zeroGKU B S hS r hp hpS a).1
  have h2 : Epi ((sheafCompose (SmallEtale.topology B S hS)
      AddCommGrpCat.uliftFunctor.{u + 1, u}).map (smallFrobMatrix B S hS r hp hpS a - 𝟙 _)) := by
    have := (Sheaf.isLocallySurjective_iff_epi' (φ := smallFrobMatrix B S hS r hp hpS a - 𝟙 _)).2 h1
    exact (Sheaf.isLocallySurjective_iff_epi' (φ := (sheafCompose (SmallEtale.topology B S hS)
      AddCommGrpCat.uliftFunctor.{u + 1, u}).map (smallFrobMatrix B S hS r hp hpS a - 𝟙 _))).1
      (isLocallySurjective_sheafCompose_uliftFunctor B S hS _)
  have h3 : Epi ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.map
      (frobMatrixMap S hp hpS a - 𝟙 _)) := by
    have : Epi ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.map
        (frobMatrixMap S hp hpS a - 𝟙 _) ≫ (freeAdditiveSheafRestrictIso B S hS r).hom) := by
      rw [freeAdditiveSheafRestrictIso_hom_comm]
      exact epi_comp _ _
    exact (epi_comp_iff_of_isIso _ _).1 this
  exact (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.epi_of_epi_map h3

include hp hpS in
/-- **The kernel of the Frobenius matrix map minus the identity of `𝐆_a^r` is constructible**, by
[Stacks, Tag 0GKU]. -/
theorem isConstructibleAbelianSheaf_kernel_frobMatrixMap_sub_id [Fact p.Prime] :
    IsConstructibleAbelianSheaf B (B.obj S hS)
      ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.obj
        (kernel (frobMatrixMap S hp hpS a - 𝟙 _))) := by
  have := preservesFiniteLimits_sheafCompose_uliftFunctor B S hS
  let G := (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse
  let L := sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}
  let e : G.obj (kernel (frobMatrixMap S hp hpS a - 𝟙 _)) ≅
      L.obj (kernel (smallFrobMatrix B S hS r hp hpS a - 𝟙 _)) :=
    PreservesKernel.iso G _ ≪≫
      kernel.mapIso _ _ (freeAdditiveSheafRestrictIso B S hS r)
        (freeAdditiveSheafRestrictIso B S hS r)
        (freeAdditiveSheafRestrictIso_hom_comm B S hS r hp hpS a) ≪≫
      (PreservesKernel.iso L _).symm
  exact isConstructibleAbelianSheaf_congr B (B.obj S hS) e.symm
    (smallFrobMatrix_zeroGKU B S hS r hp hpS a).2

end Transport

end Stacks.ArtinSchreier

end
