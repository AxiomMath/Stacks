module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialInjectiveResolution
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration

/-!
# Finite type in the next degree of a coskeletal algebra resolution

Let `A → B` be a finite type map from a Noetherian ring. If a simplicial `A`-algebra over `B` is
a trivial Kan resolution, is `n`-coskeletal, and is of finite type through degree `n`, then it is
also of finite type in degree `n + 1`.

## Main definitions

* `CommAlgCat.underlyingAugmentation`: the canonical augmentation of the underlying simplicial
  set of a simplicial `A`-algebra over `B`.

## Main results

* `CommAlgCat.finiteType_succ_of_trivialKanFibration_of_isCoskeletal`: finite type in degree
  `n + 1`.

## Implementation notes

The category of `A`-algebra maps to `B` is represented by `Over (CommAlgCat.of A B)`. The
equation `P = cosk_n sk_n P` is expressed invariantly by saying that the unit of the
truncation--coskeleton adjunction at `P` is an isomorphism.

In degree `n + 1` the coskeleton is a limit over the lower-dimensional simplices, so the maps to
the codimension-one faces are jointly monic; finite type then follows because the term embeds in
a finite product of finite type algebras onto each of whose factors it surjects.

## References

* [Stacks Project, Tag 08PW](https://stacks.math.columbia.edu/tag/08PW)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace CommAlgCat


variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

private theorem finiteType_of_injective_surjective_pi
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {I : Type v} [Finite I] {S : Type u} [CommRing S] [Algebra R S]
    (X : I → Type u) [∀ i, CommRing (X i)] [∀ i, Algebra R (X i)]
    (f : S →ₐ[R] ∀ i, X i) (hf : Function.Injective f)
    (hproj : ∀ i, Function.Surjective (fun s : S => f s i))
    (hX : ∀ i, Algebra.FiniteType R (X i)) : Algebra.FiniteType R S := by
  have : Algebra.FiniteType R (∀ i, X i) := by
    have (i : I) : Algebra.FinitePresentation R (X i) :=
      Algebra.FinitePresentation.of_finiteType.mp (hX i)
    exact Algebra.FinitePresentation.of_finiteType.mpr inferInstance
  let _ : Algebra S (∀ i, X i) := f.toRingHom.toAlgebra
  have : Module.Finite S (∀ i, X i) := by
    let _ (i : I) : Algebra S (X i) :=
      ((Pi.evalRingHom (fun i => X i) i).comp f.toRingHom).toAlgebra
    have (i : I) : Module.Finite S (X i) := RingHom.Finite.of_surjective _ (hproj i)
    exact Module.Finite.pi
  exact ⟨_root_.fg_of_fg_of_fg R S (∀ i, X i)
    (Algebra.FiniteType.out : (⊤ : Subalgebra R (∀ i, X i)).FG)
    (Module.Finite.iff_fg.mp (Module.Finite.top S _)) (fun _ _ h => hf h)⟩

private theorem exists_factor_face {n k : ℕ} (hk : k ≤ n)
    (α : SimplexCategory.mk k ⟶ SimplexCategory.mk (n + 1)) :
    ∃ (i : Fin (n + 2)) (ψ : SimplexCategory.mk k ⟶ SimplexCategory.mk n),
      α = ψ ≫ SimplexCategory.δ i := by
  have hnot : ¬ Function.Surjective α.toOrderHom := by
    intro hs
    have hc := Fintype.card_le_of_surjective α.toOrderHom hs
    simp only [Fintype.card_fin, SimplexCategory.len_mk] at hc
    omega
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 2), ∀ x, α.toOrderHom x ≠ i := by
    by_contra h
    simp only [not_exists, not_forall, not_not] at h
    exact hnot h
  exact ⟨i, SimplexCategory.eq_comp_δ_of_not_surjective' α i hi⟩

/-- In the next degree of a coskeleton, the maps to the codimension-one faces are jointly
monic. This is the limit description of the right Kan extension: every lower-dimensional map
into `[n + 1]` factors through one of those faces. -/
private theorem cosk_face_jointly_mono
    {C : Type u} [Category.{v} C] (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (U : SimplicialObject.Truncated C n) {T : C}
    {f g : T ⟶ ((SimplicialObject.Truncated.cosk n).obj U).obj (op (SimplexCategory.mk (n + 1)))}
    (h : ∀ i : Fin (n + 2),
      f ≫ ((SimplicialObject.Truncated.cosk n).obj U).map (SimplexCategory.δ i).op =
        g ≫ ((SimplicialObject.Truncated.cosk n).obj U).map (SimplexCategory.δ i).op) :
    f = g := by
  let J := (SimplexCategory.Truncated.inclusion n).op
  let X := op (SimplexCategory.mk (n + 1))
  let e := J.ranObjObjIsoLimit U X
  apply (cancel_mono e.hom).mp
  apply Limits.limit.hom_ext
  intro q
  obtain ⟨i, ψ, hα⟩ := exists_factor_face q.right.unop.property q.hom.unop
  let face : StructuredArrow X J :=
    StructuredArrow.mk (Y := op (⟨SimplexCategory.mk n, Nat.le_refl n⟩ :
      SimplexCategory.Truncated n)) (SimplexCategory.δ i).op
  let ψT : q.right.unop ⟶
      (⟨SimplexCategory.mk n, Nat.le_refl n⟩ : SimplexCategory.Truncated n) :=
    ObjectProperty.homMk ψ
  let qface : face ⟶ q := StructuredArrow.homMk ψT.op (Quiver.Hom.unop_inj hα.symm)
  have hnat :
      (J.ran.obj U).map (J.map qface.right) ≫ (J.ranCounit.app U).app q.right =
        (J.ranCounit.app U).app face.right ≫ U.map qface.right :=
    (J.ranCounit.app U).naturality qface.right
  have hfac :
      (J.ran.obj U).map q.hom ≫ (J.ranCounit.app U).app q.right =
        (J.ran.obj U).map face.hom ≫ (J.ranCounit.app U).app face.right ≫
          U.map qface.right := by
    rw [← qface.w, Functor.map_comp, Category.assoc, hnat]
  have hproj (z : T ⟶ (J.ran.obj U).obj X) :
      (z ≫ e.hom) ≫ Limits.limit.π (StructuredArrow.proj X J ⋙ U) q =
        z ≫ (J.ran.obj U).map face.hom ≫ (J.ranCounit.app U).app face.right ≫
          U.map qface.right := by
    rw [Category.assoc, Functor.ranObjObjIsoLimit_hom_π, hfac]
  have hi : f ≫ (J.ran.obj U).map face.hom = g ≫ (J.ran.obj U).map face.hom := by
    simpa [J, face, SimplicialObject.Truncated.cosk] using h i
  exact ((hproj f).trans ((reassoc_of% hi) _)).trans (hproj g).symm

/-- The canonical augmentation to `B` of the underlying simplicial set of a simplicial
`A`-algebra in the category of `A`-algebras over `B`. -/
def underlyingAugmentation (P : SimplicialObject (Over (CommAlgCat.of A B))) :
    (P ⋙ Over.forget _ ⋙ forget (CommAlgCat A)) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj B :=
  Functor.whiskerRight
    ({ app := fun j ↦ (P.obj j).hom
       naturality := fun _ _ f ↦ Over.w (P.map f) } :
      P ⋙ Over.forget _ ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj (CommAlgCat.of A B))
    (forget (CommAlgCat A))

/-- **Stacks 08PW**. For a finite type algebra `B` over a Noetherian ring `A`, an
`n`-coskeletal simplicial `A`-algebra over `B` whose canonical augmentation is a trivial Kan
fibration and whose terms through degree `n` are of finite type has a finite type term in degree
`n + 1`. -/
@[stacks 08PW]
theorem finiteType_succ_of_trivialKanFibration_of_isCoskeletal
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (P : SimplicialObject (Over (CommAlgCat.of A B))) (n : ℕ)
    (_hkan : SSet.trivialKanFibrations (underlyingAugmentation A B P))
    (hcosk : IsIso ((SimplicialObject.coskAdj n).unit.app P))
    (hfinite : ∀ k ≤ n,
      Algebra.FiniteType A (P.obj (op (SimplexCategory.mk k))).left) :
    Algebra.FiniteType A (P.obj (op (SimplexCategory.mk (n + 1)))).left := by
  let U := (SimplicialObject.truncation n).obj P
  let Q := (SimplicialObject.Truncated.cosk n).obj U
  let iTop : SimplexCategoryᵒᵖ := op (SimplexCategory.mk (n + 1))
  let M := Q.obj iTop
  let N := Q.obj (op (SimplexCategory.mk n))
  let ε := ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app U).app
    (op (⟨SimplexCategory.mk n, Nat.le_refl n⟩ : SimplexCategory.Truncated n))
  have hN : Algebra.FiniteType A N.left := Algebra.FiniteType.equiv (hfinite n le_rfl)
    (CommAlgCat.algEquivOfIso ((Over.forget (CommAlgCat.of A B)).mapIso (asIso ε))).symm
  let ρ : M.left →ₐ[A] ∀ i : Fin (n + 2), N.left :=
    AlgHom.pi (fun i => ((Q.map (SimplexCategory.δ i).op).left.hom))
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    have hcomm (i : Fin (n + 2)) (z : M.left) :
        N.hom.hom (((Q.map (SimplexCategory.δ i).op).left.hom) z) = M.hom.hom z := by
      have hw :
          AlgHom.comp N.hom.hom ((Q.map (SimplexCategory.δ i).op).left.hom) = M.hom.hom := by
        have hw' := congrArg
          (fun f : CommAlgCat.of A M.left ⟶ CommAlgCat.of A B => f.hom)
          (Over.w (Q.map (SimplexCategory.δ i).op))
        change AlgHom.comp N.hom.hom ((Q.map (SimplexCategory.δ i).op).left.hom) = M.hom.hom at hw'
        exact hw'
      simpa only [AlgHom.comp_apply] using congrArg (fun f => f z) hw
    have hcoord : ((Q.map (SimplexCategory.δ (0 : Fin (n + 2))).op).left.hom) x =
        ((Q.map (SimplexCategory.δ (0 : Fin (n + 2))).op).left.hom) y := by
      simpa [ρ] using congrFun hxy 0
    have hbase : M.hom.hom x = M.hom.hom y :=
      (hcomm 0 x).symm.trans ((congrArg N.hom.hom hcoord).trans (hcomm 0 y))
    let b : B := M.hom.hom x
    let T : Over (CommAlgCat.of A B) :=
      Over.mk (CommAlgCat.ofHom (Polynomial.aeval (R := A) b))
    let lift (z : M.left) (hz : M.hom.hom z = b) : T ⟶ M :=
      Over.homMk (CommAlgCat.ofHom (Polynomial.aeval z)) (by
        apply CommAlgCat.hom_ext
        apply Polynomial.algHom_ext
        simp [T, hz, Polynomial.aeval_def])
    let fx := lift x rfl
    let fy := lift y hbase.symm
    have hfaces : ∀ i : Fin (n + 2),
        fx ≫ Q.map (SimplexCategory.δ i).op = fy ≫ Q.map (SimplexCategory.δ i).op := by
      intro i
      apply Over.OverMorphism.ext
      apply CommAlgCat.hom_ext
      apply Polynomial.algHom_ext
      simpa [fx, fy, lift, ρ] using congrFun hxy i
    have hmaps := cosk_face_jointly_mono n U (T := T) (f := fx) (g := fy) hfaces
    have hev := congrArg (fun f : T ⟶ M => f.left.hom Polynomial.X) hmaps
    calc
      x = Polynomial.aeval x Polynomial.X := by simp
      _ = Polynomial.aeval y Polynomial.X := hev
      _ = y := by simp
  have hρsurj : ∀ i : Fin (n + 2), Function.Surjective (fun x : M.left => ρ x i) := by
    intro i y
    let j : Fin (n + 1) := i.lastCases (Fin.last n) (fun j => j)
    refine ⟨((Q.map (SimplexCategory.σ j).op).left.hom y), ?_⟩
    have hsec : Q.σ j ≫ Q.δ i = 𝟙 _ := by
      cases i using Fin.lastCases with
      | last => simpa [j] using Q.δ_comp_σ_succ (i := Fin.last n)
      | cast k => simpa [j] using Q.δ_comp_σ_self (i := k)
    have hsec' := congrArg (fun f => f.left.hom) hsec
    exact congrArg (fun f => f y) hsec'
  have hM : Algebra.FiniteType A M.left :=
    finiteType_of_injective_surjective_pi (X := fun _ : Fin (n + 2) => N.left) ρ hρinj hρsurj
      fun _ => hN
  exact Algebra.FiniteType.equiv hM (CommAlgCat.algEquivOfIso
    ((Over.forget (CommAlgCat.of A B)).mapIso
      (asIso (((SimplicialObject.coskAdj n).unit.app P).app iTop)))).symm

end CommAlgCat

end
