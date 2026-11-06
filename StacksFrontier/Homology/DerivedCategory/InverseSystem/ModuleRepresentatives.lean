module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexKernels
public import Mathlib.Algebra.Homology.HomotopyFiber
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksCore.Tactic.StacksAttribute

/-!
# Representatives of derived inverse systems with surjective transitions

Let `A : ℕᵒᵖ ⥤ RingCat` be an inverse system of rings; its compatible inverse systems of modules
form the abelian category `PresheafOfModules A`. Every object of the derived category of such
systems is represented by a cochain complex whose transition maps
`(M.X i).map (op (n + 1) ⟶ op n)` are surjective in every index `n` and every cochain degree `i`.

The representative is built from the diagonal mono of a complex into the system of finite partial
products `∏_{j ≤ n} M_j`, whose transition maps are projections and hence surjective. The mapping
cocone of the cokernel projection of that mono is quasi-isomorphic to the given object and has
surjective transition maps in every degree, since surjectivity passes to cokernels and to the
biproducts making up a mapping cocone.

## Main definitions

Nothing is exported beyond the main result: the partial-product system, the diagonal map and the
mapping-cocone representative are private to the construction.

## Main results

* `ModuleSystemRepresentative.exists_representative_with_surjective_transition_maps`: every
  object of `D(Mod(ℕ, (Aₙ)))` is `DerivedCategory.Q` of a complex whose transition maps are
  surjective in every degree.

## Implementation notes

The Stacks source indexes its systems starting at one; here index `n` represents source index
`n + 1`. Surjectivity of a transition map of complexes is stated on the underlying function in
every cochain degree. The module universe `v` and the ring universe `u` are independent, and the
derived category is an arbitrary `HasDerivedCategory.{w}` instance.

## References

* [Stacks: Tag 091F](https://stacks.math.columbia.edu/tag/091F)
-/
section

open CategoryTheory Opposite Limits Pretriangulated

universe u v w

set_option backward.isDefEq.respectTransparency false

namespace ModuleSystemRepresentative

variable {A : ℕᵒᵖ ⥤ RingCat.{u}}

private def ringToEarlier (n : ℕ) (j : Fin (n + 1)) : A.obj (op n) →+* A.obj (op j.val) :=
  (A.map ((homOfLE (Nat.le_of_lt_succ j.isLt)).op)).hom

private def earlierIndex {m n : ℕ} (h : m ≤ n) (j : Fin (m + 1)) : Fin (n + 1) :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_succ h)⟩

private def toEarlier (n : ℕ) (j : Fin (n + 1)) : op n ⟶ op j.val :=
  (homOfLE (Nat.le_of_lt_succ j.isLt)).op

private noncomputable def prodAb (M : PresheafOfModules.{v} A) : ℕᵒᵖ ⥤ Ab.{v} where
  obj X := AddCommGrpCat.of ((j : Fin (X.unop + 1)) → M.obj (op j.val))
  map {X Y} f :=
    AddCommGrpCat.ofHom <| AddMonoidHom.mk'
      (fun x j => x (earlierIndex (leOfHom f.unop) j)) (by intros; funext j; rfl)
  map_id X := by
    ext x j
    rfl
  map_comp f g := by
    ext x j
    rfl

private noncomputable def prodModule (M : PresheafOfModules.{v} A) (X : ℕᵒᵖ) :
    Module (A.obj X) ((prodAb M).obj X) := by
  change Module (A.obj X) ((j : Fin (X.unop + 1)) → M.obj (op j.val))
  letI (j : Fin (X.unop + 1)) : Module (A.obj X) (M.obj (op j.val)) :=
    Module.compHom _ (ringToEarlier X.unop j)
  infer_instance

private noncomputable def prodPresheaf (M : PresheafOfModules.{v} A) :
    PresheafOfModules.{v} A := by
  letI (X : ℕᵒᵖ) := prodModule M X
  exact PresheafOfModules.ofPresheaf (prodAb M) (by
    intro X Y f r x
    let : Module (A.obj Y) ((j : Fin (Y.unop + 1)) → M.obj (op j.val)) := prodModule M Y
    let y : (j : Fin (Y.unop + 1)) → M.obj (op j.val) :=
      fun j => x (earlierIndex (leOfHom f.unop) j)
    change (fun j : Fin (Y.unop + 1) => (r • x) (earlierIndex (leOfHom f.unop) j)) =
      ((A.map f).hom r) • y
    funext j
    rw [show (r • x) (earlierIndex (leOfHom f.unop) j) =
        (ringToEarlier X.unop (earlierIndex (leOfHom f.unop) j) r) •
          x (earlierIndex (leOfHom f.unop) j) from rfl,
      show (((A.map f).hom r) • y) j = (ringToEarlier Y.unop j ((A.map f).hom r)) • y j from rfl]
    simp only [ringToEarlier, earlierIndex, y]
    congr 1
    let g : Y ⟶ op j.val := (homOfLE (Nat.le_of_lt_succ j.isLt)).op
    let h : X ⟶ op j.val := (homOfLE (Nat.le_trans (Nat.le_of_lt_succ j.isLt)
      (leOfHom f.unop))).op
    change (A.map h).hom r = (A.map g).hom ((A.map f).hom r)
    rw [show h = f ≫ g from Subsingleton.elim _ _]
    simp)

/-- Scalars act on a partial product componentwise, through the transition ring maps. -/
private lemma prodPresheaf_smul_apply (M : PresheafOfModules.{v} A) (X : ℕᵒᵖ) (r : A.obj X)
    (x : (prodPresheaf M).obj X) (j : Fin (X.unop + 1)) :
    (r • x) j = ringToEarlier X.unop j r • x j := rfl

private noncomputable def prodAbMap {M N : PresheafOfModules.{v} A} (φ : M ⟶ N) :
    prodAb M ⟶ prodAb N where
  app X := AddCommGrpCat.ofHom <| AddMonoidHom.mk'
    (fun x j => φ.app (op j.val) (x j)) (by intros; funext j; simp)
  naturality X Y f := by
    ext x
    rfl

private noncomputable def prodMap {M N : PresheafOfModules.{v} A} (φ : M ⟶ N) :
    prodPresheaf M ⟶ prodPresheaf N := by
  refine PresheafOfModules.homMk (M₁ := prodPresheaf M) (M₂ := prodPresheaf N) ?_ ?_
  · exact prodAbMap φ
  intro X r x
  change (fun j : Fin (X.unop + 1) => φ.app (op j.val) ((r • x) j)) =
    r • (show (prodPresheaf N).obj X from fun j => φ.app (op j.val) (x j))
  funext j
  rw [prodPresheaf_smul_apply, prodPresheaf_smul_apply]
  exact (φ.app (op j.val)).hom.map_smul _ _

private noncomputable def prodFunctor :
    PresheafOfModules.{v} A ⥤ PresheafOfModules.{v} A where
  obj := prodPresheaf
  map := prodMap
  map_id M := by
    ext X x
    rfl
  map_comp φ ψ := by
    ext X x
    rfl

private noncomputable def diagAb (M : PresheafOfModules.{v} A) :
    M.presheaf ⟶ prodAb M where
  app X := AddCommGrpCat.ofHom <| AddMonoidHom.mk'
    (fun x j => M.map (toEarlier X.unop j) x) (by intros; funext j; simp)
  naturality X Y f := by
    ext x
    change (fun j : Fin (Y.unop + 1) => M.map (toEarlier Y.unop j) (M.map f x)) =
      (fun j : Fin (Y.unop + 1) =>
        M.map (toEarlier X.unop (earlierIndex (leOfHom f.unop) j)) x)
    funext j
    let g := toEarlier Y.unop j
    let h := toEarlier X.unop (earlierIndex (leOfHom f.unop) j)
    calc
      M.map g (M.map f x) = M.map (f ≫ g) x := (M.map_comp_apply f g x).symm
      _ = M.map h x := by rw [show f ≫ g = h from Subsingleton.elim _ _]; rfl

private noncomputable def diag (M : PresheafOfModules.{v} A) :
    M ⟶ prodPresheaf M := by
  refine PresheafOfModules.homMk (M₁ := M) (M₂ := prodPresheaf M) ?_ ?_
  · exact diagAb M
  intro X r x
  change (fun j : Fin (X.unop + 1) => M.map (toEarlier X.unop j) (r • x)) =
    r • (show (prodPresheaf M).obj X from fun j => M.map (toEarlier X.unop j) x)
  funext j
  rw [prodPresheaf_smul_apply]
  exact M.map_smul (toEarlier X.unop j) r x

private lemma mono_diag (M : PresheafOfModules.{v} A) : Mono (diag M) := by
  apply PresheafOfModules.mono_of_injective
  intro X x y h
  let j : Fin (X.unop + 1) := ⟨X.unop, Nat.lt_succ_self _⟩
  have hh : M.map (toEarlier X.unop j) x = M.map (toEarlier X.unop j) y :=
    congrArg (fun z : (prodPresheaf M).obj X => z j) h
  rwa [show toEarlier X.unop j = 𝟙 X from Subsingleton.elim _ _, M.map_id] at hh

private noncomputable def diagNat : 𝟭 (PresheafOfModules.{v} A) ⟶ prodFunctor where
  app M := diag M
  naturality M N φ := by
    ext X x
    change (fun j : Fin (X.unop + 1) => N.map (toEarlier X.unop j) (φ.app X x)) =
      (fun j : Fin (X.unop + 1) => φ.app (op j.val) (M.map (toEarlier X.unop j) x))
    funext j
    exact (PresheafOfModules.naturality_apply φ (toEarlier X.unop j) x).symm

private lemma prod_transition_surjective (M : PresheafOfModules.{v} A) (n : ℕ) :
    Function.Surjective ((prodPresheaf M).map ((homOfLE (Nat.le_succ n)).op)) := by
  intro y
  let x : (prodPresheaf M).obj (op (n + 1)) :=
    fun j => if h : j.val ≤ n then y ⟨j.val, Nat.lt_succ_of_le h⟩ else 0
  refine ⟨x, ?_⟩
  show (fun j : Fin (n + 1) => x (earlierIndex (Nat.le_succ n) j)) = y
  funext j
  simp [x, earlierIndex, Nat.le_of_lt_succ j.isLt]

private theorem prodPreservesZeroMorphisms : (prodFunctor : PresheafOfModules.{v} A ⥤
  PresheafOfModules.{v} A).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext X x
    rfl

private noncomputable def prodComplex (K : CochainComplex (PresheafOfModules.{v} A) ℤ) :
    CochainComplex (PresheafOfModules.{v} A) ℤ := by
  letI : (prodFunctor : PresheafOfModules.{v} A ⥤ PresheafOfModules.{v} A).PreservesZeroMorphisms :=
    prodPreservesZeroMorphisms
  exact (prodFunctor.mapHomologicalComplex (.up ℤ)).obj K

private noncomputable def diagComplex (K : CochainComplex (PresheafOfModules.{v} A) ℤ) :
    K ⟶ prodComplex K := by
  letI : (prodFunctor : PresheafOfModules.{v} A ⥤ PresheafOfModules.{v} A).PreservesZeroMorphisms :=
    prodPreservesZeroMorphisms
  exact (diagNat.mapHomologicalComplex (.up ℤ)).app K

private lemma mono_diagComplex (K : CochainComplex (PresheafOfModules.{v} A) ℤ) :
    Mono (diagComplex K) :=
  HomologicalComplex.mono_of_mono_f _ fun i => mono_diag (K.X i)

private lemma cokernel_π_f_epi (K L : CochainComplex (PresheafOfModules.{v} A) ℤ)
    (φ : K ⟶ L) (i : ℤ) : Epi ((cokernel.π φ).f i) := by
  let F := HomologicalComplex.eval (PresheafOfModules.{v} A) (.up ℤ) i
  have : PreservesColimit (parallelPair φ 0) F :=
    HomologicalComplex.eval_preservesColimit_of_hasCokernel_f φ i
  show Epi (F.map (cokernel.π φ))
  rw [← π_comp_cokernelComparison φ F]
  infer_instance

private lemma cokernel_transition_surjective
    (K L : CochainComplex (PresheafOfModules.{v} A) ℤ) (φ : K ⟶ L)
    (hL : ∀ (n : ℕ) (i : ℤ), Function.Surjective
      ((L.X i).map ((homOfLE (Nat.le_succ n)).op)))
    (n : ℕ) (i : ℤ) :
    Function.Surjective (((cokernel φ).X i).map ((homOfLE (Nat.le_succ n)).op)) := by
  have : Epi ((cokernel.π φ).f i) := cokernel_π_f_epi K L φ i
  intro q
  obtain ⟨p, hp⟩ := PresheafOfModules.surjective_of_epi ((cokernel.π φ).f i) (op n) q
  obtain ⟨p', hp'⟩ := hL n i p
  refine ⟨((cokernel.π φ).f i).app (op (n + 1)) p', ?_⟩
  rw [← PresheafOfModules.naturality_apply ((cokernel.π φ).f i)
    ((homOfLE (Nat.le_succ n)).op) p', hp', hp]

private lemma biprod_transition_surjective (P Q : PresheafOfModules.{v} A)
    (n : ℕ)
    (hP : Function.Surjective (P.map ((homOfLE (Nat.le_succ n)).op)))
    (hQ : Function.Surjective (Q.map ((homOfLE (Nat.le_succ n)).op))) :
    Function.Surjective ((P ⊞ Q).map ((homOfLE (Nat.le_succ n)).op)) := by
  intro y
  let f : op (n + 1) ⟶ op n := (homOfLE (Nat.le_succ n)).op
  obtain ⟨p, hp⟩ := hP ((biprod.fst : P ⊞ Q ⟶ P).app (op n) y)
  obtain ⟨q, hq⟩ := hQ ((biprod.snd : P ⊞ Q ⟶ Q).app (op n) y)
  refine ⟨((biprod.inl : P ⟶ P ⊞ Q).app (op (n + 1)) p) +
      ((biprod.inr : Q ⟶ P ⊞ Q).app (op (n + 1)) q), ?_⟩
  simp only [map_add]
  show (P ⊞ Q).map f ((biprod.inl : P ⟶ P ⊞ Q).app (op (n + 1)) p) +
      (P ⊞ Q).map f ((biprod.inr : Q ⟶ P ⊞ Q).app (op (n + 1)) q) = y
  rw [← PresheafOfModules.naturality_apply (biprod.inl : P ⟶ P ⊞ Q) f p,
    ← PresheafOfModules.naturality_apply (biprod.inr : Q ⟶ P ⊞ Q) f q, hp, hq]
  exact congrArg (fun t : P ⊞ Q ⟶ P ⊞ Q => t.app (op n) y) (biprod.total (X := P) (Y := Q))

private lemma cocone_transition_surjective
    {K L : CochainComplex (PresheafOfModules.{v} A) ℤ} (φ : K ⟶ L)
    (hK : ∀ n i, Function.Surjective ((K.X i).map ((homOfLE (Nat.le_succ n)).op)))
    (hL : ∀ n i, Function.Surjective ((L.X i).map ((homOfLE (Nat.le_succ n)).op)))
    (n : ℕ) (i : ℤ) :
    Function.Surjective (((CochainComplex.mappingCocone φ).X i).map
      ((homOfLE (Nat.le_succ n)).op)) := by
  have heq : (CochainComplex.mappingCocone φ).X i = (K.X i ⊞ L.X (i - 1)) := by
    simp [CochainComplex.mappingCocone, CochainComplex.mappingCone,
      HomologicalComplex.homotopyCofiber, HomologicalComplex.homotopyCofiber.X, sub_eq_add_neg]
  rw [heq]
  exact biprod_transition_surjective (K.X i) (L.X (i - 1)) n (hK n i) (hL n (i - 1))

private noncomputable def fiberIso (K : CochainComplex (PresheafOfModules.{v} A) ℤ)
    [HasDerivedCategory.{w} (PresheafOfModules.{v} A)] :
    DerivedCategory.Q.obj K ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCocone (cokernel.π (diagComplex K))) := by
  let φ := diagComplex K
  let π := cokernel.π φ
  let S : ShortComplex (CochainComplex (PresheafOfModules.{v} A) ℤ) :=
    ShortComplex.mk φ π (cokernel.condition φ)
  haveI : Mono φ := mono_diagComplex K
  have hS : S.ShortExact := ⟨ShortComplex.exact_cokernel φ⟩
  let T₁ := DerivedCategory.triangleOfSES hS
  let T₂ := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle π)
  have hT₁ : T₁.rotate ∈ distTriang _ :=
    (rotate_distinguished_triangle T₁).mp (DerivedCategory.triangleOfSES_distinguished hS)
  have hT₂ : T₂.rotate ∈ distTriang _ :=
    (rotate_distinguished_triangle T₂).mp
      (DerivedCategory.mappingCocone_triangle_distinguished π)
  let e := isoTriangleOfIso₁₂ T₁.rotate T₂.rotate hT₁ hT₂
    (Iso.refl _) (Iso.refl _) (by simp [T₁, T₂, S, π, Functor.mapTriangle,
      CochainComplex.mappingCocone.triangle])
  let e₃ := Triangle.π₃.mapIso e
  exact (shiftEquiv _ (1 : ℤ)).unitIso.app _ ≪≫
    (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso e₃ ≪≫
    (shiftEquiv _ (1 : ℤ)).unitIso.symm.app _

private lemma prodComplex_transition_surjective
    (K : CochainComplex (PresheafOfModules.{v} A) ℤ) (n : ℕ) (i : ℤ) :
    Function.Surjective (((prodComplex K).X i).map ((homOfLE (Nat.le_succ n)).op)) :=
  prod_transition_surjective (K.X i) n

/-- **Stacks 091F.** Every object of the derived category of inverse systems of modules over an
inverse system of rings is represented by a complex whose transition maps are surjective in
every degree. -/
@[stacks 091F]
public theorem exists_representative_with_surjective_transition_maps
    {A : ℕᵒᵖ ⥤ RingCat.{u}}
    [HasDerivedCategory.{w} (PresheafOfModules.{v} A)]
    (K : DerivedCategory (PresheafOfModules.{v} A)) :
    ∃ (M : CochainComplex (PresheafOfModules.{v} A) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ (n : ℕ) (i : ℤ),
        Function.Surjective
          ((M.X i).map ((homOfLE (Nat.le_succ n)).op)) := by
  let F := DerivedCategory.Q (C := PresheafOfModules.{v} A)
  have : F.EssSurj :=
    Localization.essSurj F
      (HomologicalComplex.quasiIso
        (PresheafOfModules.{v} A) (ComplexShape.up ℤ))
  let K₀ := F.objPreimage K
  exact ⟨_, (fiberIso K₀).symm ≪≫ F.objObjPreimageIso K,
    cocone_transition_surjective (cokernel.π (diagComplex K₀))
      (prodComplex_transition_surjective K₀)
      (cokernel_transition_surjective K₀ (prodComplex K₀) (diagComplex K₀)
        (prodComplex_transition_surjective K₀))⟩

end ModuleSystemRepresentative

end
