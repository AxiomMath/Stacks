module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDirectSums
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategory

/-!
# Direct sums in the homotopy category of differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. The homotopy category of right differential graded `A`-modules has arbitrary
direct sums, and they are the images of the direct sums of right differential graded modules.
Both are proved under the hypotheses `HasWeakSheafify J AddCommGrpCat.{m}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{m}`, under which these direct sums exist.

## Main results

* `SheafOfModules.DifferentialGradedModule.coproductHomotopy`: two morphisms out of a direct sum
  of right differential graded modules which are homotopic after every inclusion are homotopic.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.hasCoproducts`: the homotopy
  category admits arbitrary direct sums.

## References

* [Stacks Project, Tag 0FS2](https://stacks.math.columbia.edu/tag/0FS2)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
variable {A : DifferentialGradedAlgebra.{t, a} R}



private def sectionCast
    (N : DifferentialGradedModule.{t, a, m} A)
    {i j : ℤ} (h : i = j) (U : Cᵒᵖ) :
    (N.complex.X i).val.obj U →+ (N.complex.X j).val.obj U where
  toFun x := (eqToHom (congrArg (fun q => (N.complex.X q).val.obj U) h)) x
  map_zero' := map_zero _
  map_add' := map_add _

private theorem sectionCast_heq
    (N : DifferentialGradedModule.{t, a, m} A)
    {i j : ℤ} (h : i = j) (U : Cᵒᵖ) (x : (N.complex.X i).val.obj U) :
    HEq (sectionCast N h U x) x := by
  cases h
  rfl

private theorem sectionCast_naturality
    (N : DifferentialGradedModule.{t, a, m} A)
    {i j : ℤ} (h : i = j) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (N.complex.X i).val.obj U) :
    sectionCast N h V ((N.complex.X i).val.map f x) =
      (N.complex.X j).val.map f (sectionCast N h U x) := by
  cases h
  rfl

private theorem sectionCast_smul
    (N : DifferentialGradedModule.{t, a, m} A)
    {i j : ℤ} (h : i = j) (U : Cᵒᵖ) (r : R.obj.obj U) (x : (N.complex.X i).val.obj U) :
    sectionCast N h U (r • x) = r • sectionCast N h U x := by
  cases h
  rfl

private theorem moduleMul_cast_heq
    (N : DifferentialGradedModule.{t, a, m} A)
    {i j m : ℤ} (h : i = j) (U : Cᵒᵖ)
    (x : (N.complex.X i).val.obj U) (a : (A.complex.X m).val.obj U) :
    HEq (((N.mul j m).app U) (sectionCast N h U x) a)
      (((N.mul i m).app U) x a) := by
  cases h
  rfl

private def shiftedAction
    (N : DifferentialGradedModule.{t, a, m} A)
    (n m : ℤ) (U : Cᵒᵖ) :
    (N.complex.X (n - 1)).val.obj U →+
      (A.toGradedAlgebra.piece m).val.obj U →+
        (N.complex.X (n + m - 1)).val.obj U := by
  let h : (n - 1) + m = (n + m) - 1 := by omega
  exact {
    toFun := fun x => (sectionCast N h U).comp ((N.mul (n - 1) m).app U x)
    map_zero' := by ext a; simp
    map_add' := by intro x y; ext a; simp }

private theorem shiftedAction_apply
    (N : DifferentialGradedModule.{t, a, m} A)
    (n m : ℤ) (U : Cᵒᵖ) (x : (N.complex.X (n - 1)).val.obj U)
    (a : (A.toGradedAlgebra.piece m).val.obj U) :
    shiftedAction N n m U x a = sectionCast N (by omega) U
      (((N.mul (n - 1) m).app U x) a) := rfl

private def shiftedGradedModule
    (N : DifferentialGradedModule.{t, a, m} A) :
    GradedModule.{t, a, m} A.toGradedAlgebra where
  piece n := N.complex.X (n - 1)
  smul n m U := shiftedAction N n m U
  smul_smul_left n m U r x a := by
    let h : (n - 1) + m = (n + m) - 1 := by omega
    change sectionCast N h U (((N.mul (n - 1) m).app U) (r • x) a) = _
    rw [(N.mul (n - 1) m).map_smul_left]
    exact sectionCast_smul N h U r _
  smul_smul_right n m U r x a := by
    let h : (n - 1) + m = (n + m) - 1 := by omega
    change sectionCast N h U (((N.mul (n - 1) m).app U) x (r • a)) = _
    rw [(N.mul (n - 1) m).map_smul_right]
    exact sectionCast_smul N h U r _
  smul_naturality n m {U V} f x a := by
    let h : (n - 1) + m = (n + m) - 1 := by omega
    change (N.complex.X (n + m - 1)).val.map f
        (sectionCast N h U (((N.mul (n - 1) m).app U x) a)) = _
    calc
      _ = sectionCast N h V
          ((N.complex.X (n - 1 + m)).val.map f (((N.mul (n - 1) m).app U x) a)) :=
        (sectionCast_naturality N h f (((N.mul (n - 1) m).app U x) a)).symm
      _ = sectionCast N h V (((N.mul (n - 1) m).app V
          ((N.complex.X (n - 1)).val.map f x)) ((A.complex.X m).val.map f a)) :=
        congrArg (sectionCast N h V) ((N.mul (n - 1) m).naturality f x a)
  smul_mul n i j U x a b := by
    let h₁ : (n - 1) + i = (n + i) - 1 := by omega
    let h₃ : ((n + i) - 1) + j = ((n + i) + j) - 1 := by omega
    let h₄ : (n - 1) + (i + j) = (n + (i + j)) - 1 := by omega
    refine HEq.trans (sectionCast_heq N h₃ U _) ?_
    refine HEq.trans (moduleMul_cast_heq N h₁ U _ b) ?_
    refine HEq.trans (N.mul_assoc (n - 1) i j U x a b) ?_
    exact (sectionCast_heq N h₄ U _).symm
  smul_one n U x := by
    let h : (n - 1) + 0 = (n + 0) - 1 := by omega
    rw [shiftedAction_apply, DifferentialGradedAlgebra.toGradedAlgebra_one]
    exact HEq.trans (sectionCast_heq N h U _) (N.mul_one (n - 1) U x)

private def homotopyToShiftedGraded
    {M N : DifferentialGradedModule.{t, a, m} A}
    {f g : M ⟶ N} (h : Homotopy f g) :
    GradedModule.Hom
      ((forgetToGradedModule A).obj M)
      (shiftedGradedModule N) where
  app n := h.app n
  map_smul n m U x a := by
    change ((h.app (n + m)).val.app U) (((M.mul n m).app U) x a) =
      sectionCast N (by omega) U
        (((N.mul (n - 1) m).app U) (((h.app n).val.app U) x) a)
    exact eq_of_heq (HEq.trans (h.map_mul n m U x a)
      (sectionCast_heq N (by omega) U _).symm)

variable [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **Gluing homotopies out of a direct sum.** Two morphisms of right differential graded
modules out of a direct sum `∐ M` which are homotopic after every inclusion `Sigma.ι M i` are
homotopic. -/
noncomputable def coproductHomotopy
    {ι : Type m} {M : ι → DifferentialGradedModule.{t, a, m} A}
    {N : DifferentialGradedModule.{t, a, m} A}
    (f g : (∐ M) ⟶ N)
    (H : ∀ i, Homotopic ((Sigma.ι M i) ≫ f) ((Sigma.ι M i) ≫ g)) :
    Homotopy f g := by
  classical
  let chosen : ∀ i, Homotopy ((Sigma.ι M i) ≫ f) ((Sigma.ι M i) ≫ g) :=
    fun i => Classical.choice (H i)
  let F := forgetToGradedModule A
  let cc : Cofan (fun i => F.obj (M i)) :=
    Cofan.mk (F.obj (∐ M)) (fun i => F.map (Sigma.ι M i))
  let c' : Cofan (fun i => F.obj (M i)) :=
    Cofan.mk (shiftedGradedModule N) (fun i => homotopyToShiftedGraded (chosen i))
  let hc' : IsColimit cc := coproductIsColimit_graded A M
  let hmap := hc'.desc c'
  let app (n : ℤ) : (∐ M).complex.X n ⟶ N.complex.X (n - 1) :=
    hmap.app n
  refine ⟨app, ?_, ?_⟩
  · intro n m U x a
    have h := hmap.map_smul n m U x a
    change (hmap.app (n + m)).val.app U (((∐ M).mul n m).app U x a) =
      shiftedAction N n m U ((hmap.app n).val.app U x) a at h
    exact (heq_of_eq h).trans
      ((heq_of_eq (shiftedAction_apply N n m U ((hmap.app n).val.app U x) a)).trans
        (sectionCast_heq N (by omega) U
          (((N.mul (n - 1) m).app U) ((hmap.app n).val.app U x) a)))
  · intro n
    let hcdeg := coproductIsColimit_degree A M n
    apply hcdeg.hom_ext
    rintro ⟨i⟩
    let h_i := chosen i
    have hfac (k : ℤ) :
        ((Sigma.ι M i).toHomologicalComplex.f k) ≫ (app k) = h_i.app k :=
      congrArg (fun φ => φ.app k) (hc'.fac c' ⟨i⟩)
    have hcomm := h_i.comm n
    have hchain := (Sigma.ι M i).toHomologicalComplex.comm n (n + 1)
    calc
      _ = h_i.app n ≫ N.complex.d (n - 1) n +
          ((M i).complex.d n (n + 1) ≫ h_i.app (n + 1)) ≫
            eqToHom (congrArg N.complex.X (show (n + 1) - 1 = n by omega)) := by
        simpa [Hom.comp,
          HomologicalComplex.comp_f, Category.assoc] using hcomm
      _ = _ := by
        simp only [Cofan.mk, Discrete.natTrans_app]
        rw [← hfac n, ← hfac (n + 1)]
        simp only [Preadditive.comp_add, Category.assoc]
        simp only [← Category.assoc]
        rw [← hchain]

private noncomputable def quotientCofan
    (A : DifferentialGradedAlgebra.{t, a} R)
    {ι : Type m}
    (K : ι → HomotopyCategory.{t, a, m} A) :
    Cofan K := by
  let Q := HomotopyCategory.quotient A
  let M : ι → DifferentialGradedModule.{t, a, m} A := fun i => (K i).as
  exact Cofan.mk (Q.obj (∐ M)) (fun i => Q.map (Sigma.ι M i))

private noncomputable def homotopyCoproductDesc
    (A : DifferentialGradedAlgebra.{t, a} R)
    {ι : Type m}
    (K : ι → HomotopyCategory.{t, a, m} A)
    (P : HomotopyCategory.{t, a, m} A)
    (inj : ∀ i, (HomotopyCategory.quotient A).obj ((K i).as) ⟶ P) :
    (HomotopyCategory.quotient A).obj (∐ fun i => (K i).as) ⟶ P := by
  let Q := HomotopyCategory.quotient A
  exact Q.map (Sigma.desc (fun i => Q.preimage (inj i)))

private theorem homotopyCoproductDesc_fac
    (A : DifferentialGradedAlgebra.{t, a} R)
    {ι : Type m}
    (K : ι → HomotopyCategory.{t, a, m} A)
    (P : HomotopyCategory.{t, a, m} A)
    (inj : ∀ i, (HomotopyCategory.quotient A).obj ((K i).as) ⟶ P)
    (i : ι) :
    (HomotopyCategory.quotient A).map (Sigma.ι (fun i => (K i).as) i) ≫
      homotopyCoproductDesc A K P inj = inj i := by
  rw [homotopyCoproductDesc, ← Functor.map_comp, Sigma.ι_comp_desc]
  exact Functor.map_preimage _ _

private noncomputable def quotientCofanIsColimit
    (A : DifferentialGradedAlgebra.{t, a} R)
    {ι : Type m}
    (K : ι → HomotopyCategory.{t, a, m} A) :
    IsColimit (quotientCofan A K) := by
  let Q := HomotopyCategory.quotient A
  let M : ι → DifferentialGradedModule.{t, a, m} A := fun i => (K i).as
  refine Cofan.IsColimit.mk _
    (fun s => homotopyCoproductDesc A K s.pt (fun i => s.inj i))
    (fun s i => homotopyCoproductDesc_fac A K s.pt (fun i => s.inj i) i)
    (fun s m hm => ?_)
  let m' := Q.preimage m
  let d := Sigma.desc (fun i => Q.preimage (s.inj i))
  have hpre : Q.map m' = m := Q.map_preimage m
  rw [← hpre, homotopyCoproductDesc]
  apply (HomotopyCategory.quotient_map_eq_iff m' d).2
  refine ⟨coproductHomotopy m' d (fun i => ?_)⟩
  apply (HomotopyCategory.quotient_map_eq_iff
    (Sigma.ι M i ≫ m') (Sigma.ι M i ≫ d)).1
  have hmi : Q.map (Sigma.ι M i) ≫ m = s.inj i := hm i
  have hdi : Q.map (Sigma.ι M i) ≫ Q.map d = s.inj i :=
    homotopyCoproductDesc_fac A K s.pt (fun i => s.inj i) i
  rw [Functor.map_comp, Functor.map_comp, hpre, hdi]
  exact hmi

namespace HomotopyCategory

/-- The homotopy category of right differential graded modules admits arbitrary direct sums. -/
instance hasCoproducts (A : DifferentialGradedAlgebra.{t, a} R) :
    HasCoproducts.{m} (HomotopyCategory.{t, a, m} A) :=
  hasCoproducts_of_colimit_cofans (quotientCofan A) (quotientCofanIsColimit A)

end HomotopyCategory


end DifferentialGradedModule

end SheafOfModules
