module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.RingTheory.Ext.DerivedHomFiniteness

/-!
# Finiteness of Ext and of derived Hom over a Noetherian ring

Let `A` be a Noetherian ring, let `K` be an object of `D(A)` which is bounded above and has
finite cohomology modules, and let `L` be an object of `D(A)` which is bounded below and has
finite cohomology modules. Then every `Ext^i_A(K, L)` is a finite `A`-module, and every
cohomology module of `RHom_A(K, L)` is finite; in other words `RHom_A(K, L)` lies in
`D⁺_Coh(A)`.

The proof is the dévissage used by the source. For modules in a single degree finiteness is
[Stacks, Tag 08YR], available as Mathlib's `ModuleCat.finite_ext`. The canonical truncation
triangles extend that first to a bounded `L`, then — because `L` is bounded below, so that only
finitely many degrees of `K` can contribute to a fixed `Ext` — to a bounded and finally a
bounded-above `K`. Finiteness of the cohomology of `RHom_A(K, L)` follows because for a
K-injective representative `I` of `L` the degree-`i` cohomology of the Hom complex
`Hom^•(P, I)` is `Ext^i_A(K, L)`.

## Main results

* `StacksDraft.DerivedHom.finite_ext_of_isLE_of_isGE`: finiteness of `Ext^i_A(K, L)`.
* `StacksDraft.DerivedHom.finite_homology_derivedHom`: finiteness of the cohomology modules of
  `RHom_A(K, L)`, for the derived Hom bifunctor of any `DerivedHomData`.

## References

* [Stacks Project, Tag 08YR](https://stacks.math.columbia.edu/tag/08YR)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated DerivedCategory
  CochainComplex.HomComplex
open StacksDraft.DerivedHomFiniteness

namespace StacksDraft.DerivedHom

universe u w

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-! ### Dévissage of finiteness along distinguished triangles -/

section Devissage

variable [IsNoetherianRing R]

/-- `Hom(-, Y)` on a distinguished triangle: finiteness of the outer terms gives finiteness of
the middle one. -/
private lemma finite_hom_middle_of_source_triangle
    {T : Triangle (DerivedCategory (ModuleCat.{u} R))} (hT : T ∈ distTriang _)
    (Y : DerivedCategory (ModuleCat.{u} R))
    (h₁ : Module.Finite R (T.obj₁ ⟶ Y)) (h₃ : Module.Finite R (T.obj₃ ⟶ Y)) :
    Module.Finite R (T.obj₂ ⟶ Y) := by
  refine module_finite_of_exact (Linear.leftComp R Y T.mor₂) (Linear.leftComp R Y T.mor₁)
    fun x hx => ?_
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT x hx
  exact ⟨g, hg.symm⟩

end Devissage

/-! ### Finiteness of Ext out of a bounded-above object -/

section BoundedAbove

variable [IsNoetherianRing R]

/-- Shifting is a linear isomorphism on morphism modules. -/
private def shiftHomLinearEquiv (X Y : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (X ⟶ Y) ≃ₗ[R] (X⟦n⟧ ⟶ Y⟦n⟧) :=
  let F := shiftFunctor (DerivedCategory (ModuleCat.{u} R)) n
  LinearEquiv.ofBijective (F.mapLinearMap R) ⟨F.map_injective, F.map_surjective⟩

/-- Finiteness of `Ext^i` out of a finite module placed in an arbitrary degree `d`. -/
private lemma finite_ext_from_single_shift (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℤ)
    (L : DerivedCategory (ModuleCat.{u} R)) (a : ℤ) [L.IsGE a]
    (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) k).obj L)) (i : ℤ) :
    Module.Finite R
      (DerivedCategory.Ext ((singleFunctor (ModuleCat.{u} R) d).obj M) L i) := by
  let S0 := (singleFunctor (ModuleCat.{u} R) 0).obj M
  let Sd := (singleFunctor (ModuleCat.{u} R) d).obj M
  let eS : Sd ≅ S0⟦-d⟧ :=
    asIso (((singleFunctors (ModuleCat.{u} R)).shiftIso (-d) d 0 (by omega)).inv.app M)
  let eShift : (Sd ⟶ L⟦i⟧) ≃ₗ[R] (S0⟦-d⟧ ⟶ L⟦i⟧) := Linear.homCongr R eS (Iso.refl _)
  let eDom : (S0⟦-d⟧)⟦d⟧ ≅ S0 :=
    ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} R)) (-d) d 0 (by omega)).app S0).symm ≪≫
      (shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).app S0
  let eCod : (L⟦i⟧)⟦d⟧ ≅ L⟦i + d⟧ :=
    ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} R)) i d (i + d) rfl).app L).symm
  let eBoth : (S0⟦-d⟧ ⟶ L⟦i⟧) ≃ₗ[R] (S0 ⟶ L⟦i + d⟧) :=
    (shiftHomLinearEquiv (S0⟦-d⟧) (L⟦i⟧) d).trans (Linear.homCongr R eDom eCod)
  have hfin : Module.Finite R (S0 ⟶ L⟦i + d⟧) := by
    simpa [DerivedCategory.Ext] using finite_ext_of_isGE M L a hL (i + d)
  change Module.Finite R (Sd ⟶ L⟦i⟧)
  exact Module.Finite.equiv (eShift.trans eBoth).symm

/-- Finiteness of `Hom(X, L⟦i⟧)` for `X` concentrated in degree `d` with finite cohomology. -/
private lemma finite_hom_of_isGE_of_isLE (X L : DerivedCategory (ModuleCat.{u} R)) (d b : ℤ)
    [X.IsGE d] [X.IsLE d] (hX : Module.Finite R ((homologyFunctor (ModuleCat.{u} R) d).obj X))
    [L.IsGE b] (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) k).obj L)) (i : ℤ) :
    Module.Finite R (X ⟶ L⟦i⟧) := by
  obtain ⟨M, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE d
  have hM : Module.Finite R M := Module.Finite.equiv
    ((homologyFunctor (ModuleCat.{u} R) d).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) d).app M).toLinearEquiv
  have := finite_ext_from_single_shift M d L b hL i
  exact Module.Finite.equiv (Linear.homCongr R e (Iso.refl (L⟦i⟧))).symm

/-- Finiteness of `Ext^i(K, L)` for `K` bounded with finite cohomology and `L` bounded below
with finite cohomology, by induction on the width of the window containing `K`. -/
private lemma finite_ext_of_bounded_source (a : ℤ) (n : ℕ) :
    ∀ (K L : DerivedCategory (ModuleCat.{u} R)) (_ : K.IsGE a) (_ : K.IsLE (a + n))
      (_ : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) k).obj K))
      (b : ℤ) (_ : L.IsGE b)
      (_ : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) k).obj L)) (i : ℤ),
      Module.Finite R (DerivedCategory.Ext K L i) := by
  induction n with
  | zero =>
    intro K L hKge hKle hK b hLge hL i
    have : L.IsGE b := hLge
    have hKle' : K.IsLE a := by simpa using hKle
    exact finite_hom_of_isGE_of_isLE K L a b (hK a) hL i
  | succ n ih =>
    intro K L hKge hKle hK b hLge hL i
    have : L.IsGE b := hLge
    have hLE : K.IsLE (a + n + 1) := by simpa [add_assoc] using hKle
    let T := (TStructure.t.triangleLEGE (a + n) (a + n + 1) rfl).obj K
    have hT : T ∈ distTriang _ :=
      TStructure.t.triangleLEGE_distinguished (a + n) (a + n + 1) rfl K
    have h₁ : Module.Finite R (T.obj₁ ⟶ L⟦i⟧) :=
      ih ((TStructure.t.truncLE (a + n)).obj K) L
        (show TStructure.t.IsGE ((TStructure.t.truncLE (a + n)).obj K) a from inferInstance)
        (show TStructure.t.IsLE ((TStructure.t.truncLE (a + n)).obj K) (a + n) from inferInstance)
        (finite_homology_truncLE K hK _) b hLge hL i
    have h₃ : Module.Finite R (T.obj₃ ⟶ L⟦i⟧) := by
      have hGE : T.obj₃.IsGE (a + n + 1) :=
        show TStructure.t.IsGE ((TStructure.t.truncGE (a + n + 1)).obj K) (a + n + 1) from
          inferInstance
      have hle : T.obj₃.IsLE (a + n + 1) :=
        show TStructure.t.IsLE ((TStructure.t.truncGE (a + n + 1)).obj K) (a + n + 1) from
          inferInstance
      exact finite_hom_of_isGE_of_isLE T.obj₃ L (a + n + 1) b
        (finite_homology_truncGE K hK (a + n + 1) (a + n + 1)) hL i
    exact finite_hom_middle_of_source_triangle (T := T) hT (L⟦i⟧) h₁ h₃

/-- **Finiteness of `Ext` over a Noetherian ring.** Let `R` be a Noetherian ring, let `K` be an
object of `D(R)` which is bounded above and has finite cohomology modules, and let `L` be an
object of `D(R)` which is bounded below and has finite cohomology modules. Then `Ext^i_R(K, L)`
is a finite `R`-module for every `i`.

Because `L` is bounded below, the part of `K` below degree `b - i` contributes nothing to
`Ext^i`, so `K` may be replaced by a bounded truncation. -/
public lemma finite_ext_of_isLE_of_isGE (K L : DerivedCategory (ModuleCat.{u} R)) (d b : ℤ)
    (hKle : K.IsLE d) (hLge : L.IsGE b)
    (hK : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) k).obj K))
    (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) k).obj L)) (i : ℤ) :
    Module.Finite R (DerivedCategory.Ext K L i) := by
  have : L.IsGE b := hLge
  have hYge : (L⟦i⟧).IsGE (b - i) := TStructure.t.isGE_shift L b i (b - i) (by omega)
  by_cases hd : d < b - i
  · have : Subsingleton (K ⟶ L⟦i⟧) :=
      ⟨fun f g => (TStructure.t.zero f d (b - i) hd).trans
        (TStructure.t.zero g d (b - i) hd).symm⟩
    change Module.Finite R (K ⟶ L⟦i⟧)
    infer_instance
  · let a := b - i - 1
    let T := (TStructure.t.triangleLEGE a (a + 1) rfl).obj K
    have hT : T ∈ distTriang _ := TStructure.t.triangleLEGE_distinguished a (a + 1) rfl K
    have h₁ : Module.Finite R (T.obj₁ ⟶ L⟦i⟧) := by
      have hA : T.obj₁.IsLE a :=
        show TStructure.t.IsLE ((TStructure.t.truncLE a).obj K) a from inferInstance
      have : Subsingleton (T.obj₁ ⟶ L⟦i⟧) :=
        ⟨fun f g => (TStructure.t.zero f a (b - i) (by dsimp [a]; omega)).trans
          (TStructure.t.zero g a (b - i) (by dsimp [a]; omega)).symm⟩
      infer_instance
    have hCge : T.obj₃.IsGE (a + 1) :=
      show TStructure.t.IsGE ((TStructure.t.truncGE (a + 1)).obj K) (a + 1) from inferInstance
    have : K.IsLE d := hKle
    have hCle : T.obj₃.IsLE d :=
      show TStructure.t.IsLE ((TStructure.t.truncGE (a + 1)).obj K) d from inferInstance
    obtain ⟨n, hn⟩ : ∃ n : ℕ, d = (a + 1) + n := ⟨(d - (a + 1)).toNat, by dsimp [a]; omega⟩
    have hCle' : T.obj₃.IsLE ((a + 1) + n) := by simpa [hn] using hCle
    have h₃ : Module.Finite R (T.obj₃ ⟶ L⟦i⟧) :=
      finite_ext_of_bounded_source (a + 1) n T.obj₃ L hCge hCle'
        (finite_homology_truncGE K hK (a + 1)) b hLge hL i
    change Module.Finite R (K ⟶ L⟦i⟧)
    exact finite_hom_middle_of_source_triangle (T := T) hT (L⟦i⟧) h₁ h₃

end BoundedAbove

/-! ### Finiteness of the cohomology of derived Hom -/

section DerivedHom

/-- A degree-`n` cocycle of the Hom complex, read as a morphism in the homotopy category. -/
private def cocycleHomLinearMap (P I : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cocycle P I n →ₗ[R]
      ((HomotopyCategory.quotient _ _).obj P ⟶ (HomotopyCategory.quotient _ _).obj (I⟦n⟧)) :=
  (HomotopyCategory.quotient _ _).mapLinearMap R |>.comp
    (show Cocycle P I n →ₗ[R] (P ⟶ I⟦n⟧) from
      { __ := Cocycle.equivHomShift.symm.toAddMonoidHom
        map_smul' := by
          intro r z
          ext p x
          simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cocycle.rightShift_coe,
            Cochain.rightShift_v] })

variable [IsNoetherianRing R]

/-- For a K-injective target the degree-`n` cohomology of the Hom complex is the module of
morphisms into the `n`-fold shift in the derived category, so finiteness of the latter gives
finiteness of the former. -/
private lemma finite_homology_homComplex_of_finite_hom
    (P I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] (n : ℤ)
    (h : Module.Finite R (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (I⟦n⟧)))) :
    Module.Finite R ((CochainComplex.HomComplexR R P I).homology n) := by
  let S := (CochainComplex.HomComplexR R P I).sc' (n - 1) n (n + 1)
  let e : LinearMap.ker S.g.hom ≃ₗ[R] Cocycle P I n :=
    { toFun := fun z => ⟨z.val, z.property⟩
      invFun := fun z => ⟨z.val, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f := ((DerivedCategory.Qh : _ ⥤ DerivedCategory (ModuleCat.{u} R)).mapLinearMap R).comp
    ((cocycleHomLinearMap P I n).comp e.toLinearMap)
  have hf : LinearMap.ker f = LinearMap.range S.moduleCatToCycles := by
    ext z
    change f z = 0 ↔ _
    change DerivedCategory.Qh.map (CohomologyClass.toHom (CohomologyClass.mk (e z))) = 0 ↔ _
    rw [← Functor.map_zero DerivedCategory.Qh,
      (CochainComplex.IsKInjective.Qh_map_bijective _ _).injective.eq_iff,
      CohomologyClass.toHom_mk_eq_zero_iff, mem_coboundaries_iff (e z) (n - 1) (by omega)]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, Subtype.ext hb⟩, fun ⟨b, hb⟩ => ⟨b, congrArg Subtype.val hb⟩⟩
  have hker : Module.Finite R (LinearMap.ker S.g.hom ⧸ LinearMap.ker f) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  rw [hf] at hker
  have hquot : Module.Finite R S.moduleCatLeftHomologyData.H := hker
  exact Module.Finite.equiv
    (((CochainComplex.HomComplexR R P I).homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp)) ≪≫
      S.moduleCatHomologyIso).symm.toLinearEquiv

/-- **The algebra input to [Stacks, Tag 0D0C].** Over a Noetherian ring `R`, let `K` be bounded
above with finite cohomology modules and let `L` be bounded below with finite cohomology
modules. Then every cohomology module of `RHom_R(K, L)` is finite.

Taking a K-injective representative `I` of `L` identifies `H^i(RHom_R(K, L))` with
`Ext^i_R(K, L)`, which is finite by `finite_ext_of_isLE_of_isGE`. -/
public lemma finite_homology_derivedHom (D : DerivedHomData R)
    (K L : DerivedCategory (ModuleCat.{u} R)) (d b : ℤ)
    (hKle : K.IsLE d) (hLge : L.IsGE b)
    (hK : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) k).obj K))
    (hL : ∀ k, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) k).obj L)) (i : ℤ) :
    Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj (D.hom.obj (op K, L))) := by
  let P := DerivedCategory.Q.objPreimage K
  let eP := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨I, f, hf, hI⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage L)
  have := hf
  let eI : DerivedCategory.Q.obj I ≅ L :=
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso L
  let e₁ : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) ≅ K :=
    (DerivedCategory.quotientCompQhIso _).app P ≪≫ eP
  let e₂ : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (I⟦i⟧)) ≅ L⟦i⟧ :=
    (DerivedCategory.quotientCompQhIso _).app (I⟦i⟧) ≪≫
      (DerivedCategory.Q.commShiftIso i).app I ≪≫ (shiftFunctor _ i).mapIso eI
  have := finite_ext_of_isLE_of_isGE K L d b hKle hLge hK hL i
  have : Module.Finite R ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).obj
      (CochainComplex.HomComplexR R P I)) :=
    finite_homology_homComplex_of_finite_hom P I i
      (Module.Finite.equiv (Linear.homCongr R e₁ e₂).symm)
  let e : D.hom.obj (op K, L) ≅ DerivedCategory.Q.obj (CochainComplex.HomComplexR R P I) :=
    D.hom.mapIso (Iso.prod eP.op eI.symm) ≪≫ D.homIso P I
  exact Module.Finite.equiv
    ((homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫
      (homologyFunctorFactors (ModuleCat.{u} R) i).app _).symm.toLinearEquiv

end DerivedHom

end StacksDraft.DerivedHom

end
