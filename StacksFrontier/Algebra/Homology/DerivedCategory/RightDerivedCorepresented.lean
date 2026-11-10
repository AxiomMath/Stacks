module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor

/-!
# The total right derived functor of a corepresented functor is corepresented

Let `𝒜` be an abelian category and let `F : 𝒜 ⥤ Ab` be an additive functor corepresented by an
object `P` with universal element `p ∈ F(P)`: every `M` has `Hom(P, M) ≅ F(M)`, `f ↦ F(f)(p)`.
Let `RF : D(𝒜) ⥤ D(Ab)` be its total right derived functor, computed on K-injective complexes.
Then for every `n` the functor `H^n ∘ RF : D(𝒜) ⥤ Ab` is corepresented by `P` placed in degree
`n`: there is an element `e ∈ H^n(RF(P[-n]))` such that for every object `K` of `D(𝒜)`

`Hom_{D(𝒜)}(P[-n], K) ⟶ H^n(RF(K))`, `u ↦ H^n(RF(u))(e)`

is bijective. The case of interest is global sections on a ringed space, corepresented by the
structure sheaf and its section `1`, where this says
`Hom_{D(𝒪_X)}(𝒪_X[-n], K) = H^n(X, K)`, naturally in `K`.

## Main results

* `Stacks.DerivedFunctor.quotient_map_eq_zero_of_classOf_eq_zero`: on complexes, a morphism
  `P[-n] ⟶ J` inducing the zero class in `H^n(F(J))` is null-homotopic.
* `Stacks.DerivedFunctor.exists_classOf_eq`: every class in `H^n(F(J))` is induced by a morphism
  `P[-n] ⟶ J`.
* `Stacks.DerivedFunctor.bijective_homologyFunctor_map_universalClass`: the corepresentability
  of `H^n ∘ RF` described above, with universal element `universalClass`.
* `Stacks.DerivedFunctor.exists_bijective_homologyFunctor_map_rightDerived`: the corepresentability
  of `H^n ∘ RF`, in existential form.

## Implementation notes

The element `e` is the class of `p` in `H^n(F(P[-n]))`, carried along the derivation unit. By
the Yoneda form of the statement, naturality in `K` is automatic, so bijectivity has to be checked
only on one object in each isomorphism class; every object of `D(𝒜)` is isomorphic to a
K-injective complex, on which `RF` is computed by `F` itself and on which morphisms in `D(𝒜)` are
homotopy classes of morphisms of complexes (`CochainComplex.IsKInjective.Qh_map_bijective`). For a
complex `J`, morphisms `P[-n] ⟶ J` are the morphisms `P ⟶ Jⁿ` killed by the differential, that is
the cycles of `F(J)` in degree `n`, and such a morphism is null-homotopic exactly when it factors
through `J^{n-1}`, that is when the cycle is a boundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

universe w w' v u

namespace Stacks.DerivedFunctor

variable {A : Type u} [Category.{v} A] [Abelian A]
  (F : A ⥤ AddCommGrpCat.{v}) [F.Additive]
  (P : A) (p : F.obj P)

section Complexes

variable (n : ℤ)

/-- `P` placed in degree `n`, as a cochain complex. -/
abbrev singleComplex : CochainComplex A ℤ := (CochainComplex.singleFunctor A n).obj P

/-- The image of `F` on a cochain complex. -/
abbrev mapComplex (J : CochainComplex A ℤ) : CochainComplex AddCommGrpCat.{v} ℤ :=
  (F.mapHomologicalComplex (.up ℤ)).obj J

omit [F.Additive] in
/-- A cycle of a cochain complex of abelian groups is determined by the underlying element. -/
theorem cycles_ext {L : CochainComplex AddCommGrpCat.{v} ℤ} {c c' : L.cycles n}
    (h : L.iCycles n c = L.iCycles n c') : c = c' :=
  (AddCommGrpCat.mono_iff_injective _).1 inferInstance h

/-- The cycle of `F(P[-n])` in degree `n` given by `p`. -/
def unitCycle : (mapComplex F (singleComplex P n)).cycles n :=
  (ShortComplex.abCyclesIso ((mapComplex F (singleComplex P n)).sc n)).inv
    ⟨F.map (HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv p, by
      change (F.map _ ≫ F.map _) p = 0
      rw [← F.map_comp]
      simp⟩

/-- The underlying element of `unitCycle` is the image of `p` in `F(P[-n])ⁿ`. -/
theorem iCycles_unitCycle :
    (mapComplex F (singleComplex P n)).iCycles n (unitCycle F P p n) =
      F.map (HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv p :=
  ShortComplex.abCyclesIso_inv_apply_iCycles _ _

/-- The class of `p` in `H^n(F(P[-n]))`. -/
def unitClass : (mapComplex F (singleComplex P n)).homology n :=
  (mapComplex F (singleComplex P n)).homologyπ n (unitCycle F P p n)

/-- The class induced in `H^n(F(J))` by a morphism `P[-n] ⟶ J` of complexes. -/
def classOf {J : CochainComplex A ℤ} (φ : singleComplex P n ⟶ J) :
    (mapComplex F J).homology n :=
  HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ) n (unitClass F P p n)

/-- The class induced by `φ` is the class of a cycle whose underlying element is `F(φⁿ)(p)`. -/
theorem exists_cycle_classOf {J : CochainComplex A ℤ} (φ : singleComplex P n ⟶ J) :
    ∃ c : (mapComplex F J).cycles n, (mapComplex F J).homologyπ n c = classOf F P p n φ ∧
      (mapComplex F J).iCycles n c =
        F.map ((HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv ≫ φ.f n) p := by
  refine ⟨HomologicalComplex.cyclesMap ((F.mapHomologicalComplex (.up ℤ)).map φ) n
    (unitCycle F P p n), ?_, ?_⟩
  · simp only [classOf, unitClass, ← ConcreteCategory.comp_apply,
      HomologicalComplex.homologyπ_naturality]
  · rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
      iCycles_unitCycle F P p n, F.map_comp, ConcreteCategory.comp_apply]
    rfl

/-- The class induced by a difference of morphisms is the difference of their classes. -/
theorem classOf_sub {J : CochainComplex A ℤ} (φ ψ : singleComplex P n ⟶ J) :
    classOf F P p n (φ - ψ) = classOf F P p n φ - classOf F P p n ψ := by
  simp [classOf, HomologicalComplex.homologyMap_sub]

variable (hP : ∀ M : A, Function.Bijective (fun f : P ⟶ M => F.map f p))
include hP

/-- **Every class of `H^n(F(J))` is induced by a morphism `P[-n] ⟶ J`.** -/
theorem exists_classOf_eq (J : CochainComplex A ℤ) (h : (mapComplex F J).homology n) :
    ∃ φ : singleComplex P n ⟶ J, classOf F P p n φ = h := by
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (inferInstance : Epi ((mapComplex F J).homologyπ n)) h
  obtain ⟨f, hf⟩ := (hP (J.X n)).2 ((mapComplex F J).iCycles n c)
  replace hf : F.map f p = (mapComplex F J).iCycles n c := hf
  have hd : f ≫ J.d n (n + 1) = 0 := by
    refine (hP _).1 ?_
    dsimp only
    rw [F.map_comp, ConcreteCategory.comp_apply, hf, F.map_zero]
    change ((mapComplex F J).iCycles n ≫ (mapComplex F J).d n (n + 1)) c = 0
    rw [HomologicalComplex.iCycles_d]
    rfl
  have hd' : ∀ k, (ComplexShape.up ℤ).Rel n k → f ≫ J.d n k = 0 := fun k hk => by
    obtain rfl : k = n + 1 := by simpa using hk.symm
    exact hd
  refine ⟨HomologicalComplex.mkHomFromSingle f hd', ?_⟩
  obtain ⟨c', hc', hc'i⟩ := exists_cycle_classOf F P p n (HomologicalComplex.mkHomFromSingle f hd')
  rw [← hc']
  congr 1
  refine cycles_ext n ?_
  rw [hc'i, HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc]
  exact hf

/-- **A morphism `P[-n] ⟶ J` inducing the zero class is null-homotopic.** -/
theorem quotient_map_eq_zero_of_classOf_eq_zero {J : CochainComplex A ℤ}
    (φ : singleComplex P n ⟶ J) (h : classOf F P p n φ = 0) :
    (HomotopyCategory.quotient A (.up ℤ)).map φ = 0 := by
  obtain ⟨c, hc, hci⟩ := exists_cycle_classOf F P p n φ
  rw [h] at hc
  have hex : (ShortComplex.mk _ _ ((mapComplex F J).toCycles_comp_homologyπ (n - 1) n)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ ((mapComplex F J).homologyIsCokernel (n - 1) n (by simp))
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1 hex c hc
  obtain ⟨g, rfl⟩ := (hP (J.X (n - 1))).2 y
  replace hy : (mapComplex F J).toCycles (n - 1) n (F.map g p) = c := hy
  have hg : g ≫ J.d (n - 1) n = (HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv ≫ φ.f n := by
    refine (hP _).1 ?_
    dsimp only
    rw [← hci, ← hy, F.map_comp, ConcreteCategory.comp_apply]
    change _ = ((mapComplex F J).toCycles (n - 1) n ≫ (mapComplex F J).iCycles n) _
    rw [HomologicalComplex.toCycles_i]
    rfl
  rw [HomotopyCategory.quotient_map_eq_zero_iff]
  refine ⟨(Cochain.equivHomotopy φ 0).symm ⟨Cochain.fromSingleMk g (show n + (-1) = n - 1 by lia),
    ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero, Cochain.δ_fromSingleMk _ _ _ n (by lia), hg]
  refine (Cochain.fromSingleEquiv (show n + 0 = n by lia)).injective ?_
  simp [Cochain.fromSingleEquiv, Cochain.fromSingleMk_v]

end Complexes

section Derived

open DerivedCategory

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} AddCommGrpCat.{v}]
  (R : DerivedCategory A ⥤ DerivedCategory AddCommGrpCat.{v})
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ R) (n : ℤ)

/-- Degree-`n` cohomology of a complex of abelian groups, read in the derived category through
the homotopy category, is its degree-`n` homology. -/
def homologyQhIso (L : CochainComplex AddCommGrpCat.{v} ℤ) :
    (homologyFunctor AddCommGrpCat.{v} n).obj
        (Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj L)) ≅ L.homology n :=
  (homologyFunctor AddCommGrpCat.{v} n).mapIso ((quotientCompQhIso _).app L) ≪≫
    (homologyFunctorFactors _ n).app L

/-- The isomorphism `homologyQhIso` is natural in the complex, in its `hom` direction. -/
theorem homologyQhIso_hom_naturality {L L' : CochainComplex AddCommGrpCat.{v} ℤ} (ψ : L ⟶ L') :
    (homologyFunctor AddCommGrpCat.{v} n).map
        (Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map ψ)) ≫ (homologyQhIso n L').hom =
      (homologyQhIso n L).hom ≫ HomologicalComplex.homologyMap ψ n := by
  have h1 : (homologyFunctor AddCommGrpCat.{v} n).map (Q.map ψ) ≫
      (homologyFunctorFactors AddCommGrpCat.{v} n).hom.app L' =
        (homologyFunctorFactors AddCommGrpCat.{v} n).hom.app L ≫
          HomologicalComplex.homologyMap ψ n :=
    (homologyFunctorFactors AddCommGrpCat.{v} n).hom.naturality ψ
  have h2 : Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map ψ) ≫
      (quotientCompQhIso AddCommGrpCat.{v}).hom.app L' =
        (quotientCompQhIso AddCommGrpCat.{v}).hom.app L ≫ Q.map ψ :=
    (quotientCompQhIso AddCommGrpCat.{v}).hom.naturality ψ
  change _ ≫ ((homologyFunctor AddCommGrpCat.{v} n).map
      ((quotientCompQhIso AddCommGrpCat.{v}).hom.app L') ≫
        (homologyFunctorFactors AddCommGrpCat.{v} n).hom.app L') =
    ((homologyFunctor AddCommGrpCat.{v} n).map
      ((quotientCompQhIso AddCommGrpCat.{v}).hom.app L) ≫
        (homologyFunctorFactors AddCommGrpCat.{v} n).hom.app L) ≫ _
  simp only [← Functor.map_comp_assoc, h2]
  simp only [Functor.map_comp, Category.assoc, h1]
  exact (Category.assoc _ _ _).symm

/-- The isomorphism `homologyQhIso` is natural in the complex, in its `inv` direction. -/
theorem homologyQhIso_inv_naturality {L L' : CochainComplex AddCommGrpCat.{v} ℤ} (ψ : L ⟶ L') :
    (homologyQhIso n L).inv ≫ (homologyFunctor AddCommGrpCat.{v} n).map
        (Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map ψ)) =
      HomologicalComplex.homologyMap ψ n ≫ (homologyQhIso n L').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, homologyQhIso_hom_naturality]

/-- The comparison `Qh(P[-n]) ≅ P[-n]` in `D(𝒜)`. -/
def singleQhIso :
    Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj (singleComplex P n)) ≅
      (singleFunctor A n).obj P :=
  (quotientCompQhIso A).app _ ≪≫ ((singleFunctorIsoCompQ A n).app P).symm

/-- The universal element `e ∈ H^n(RF(P[-n]))`: the class of `p`, carried along the
derivation unit. -/
def universalClass :
    (homologyFunctor AddCommGrpCat.{v} n).obj (R.obj ((singleFunctor A n).obj P)) :=
  ((homologyQhIso n (mapComplex F (singleComplex P n))).inv ≫
    (homologyFunctor AddCommGrpCat.{v} n).map
      (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj (singleComplex P n)) ≫
        R.map (singleQhIso P n).hom)) (unitClass F P p n)

/-- On a morphism induced by a morphism of complexes `φ : P[-n] ⟶ J`, the map
`u ↦ H^n(RF(u))(e)` is the class of `φ`, carried along the derivation unit at `J`. -/
theorem homologyFunctor_map_universalClass {J : CochainComplex A ℤ}
    (φ : singleComplex P n ⟶ J) :
    (homologyFunctor AddCommGrpCat.{v} n).map
        (R.map ((singleQhIso P n).inv ≫ Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map φ)))
        (universalClass F P p R β n) =
      (homologyFunctor AddCommGrpCat.{v} n).map
        (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj J))
        ((homologyQhIso n (mapComplex F J)).inv (classOf F P p n φ)) := by
  have hnat := β.naturality ((HomotopyCategory.quotient A (.up ℤ)).map φ)
  dsimp only [Functor.comp_map] at hnat
  have key : ((homologyQhIso n (mapComplex F (singleComplex P n))).inv ≫
      (homologyFunctor AddCommGrpCat.{v} n).map
        (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj (singleComplex P n)) ≫
          R.map (singleQhIso P n).hom)) ≫ (homologyFunctor AddCommGrpCat.{v} n).map
        (R.map ((singleQhIso P n).inv ≫ Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map φ))) =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ) n ≫
        (homologyQhIso n (mapComplex F J)).inv ≫ (homologyFunctor AddCommGrpCat.{v} n).map
          (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj J)) := by
    have e1 : (homologyFunctor AddCommGrpCat.{v} n).map
          (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj (singleComplex P n)) ≫
            R.map (singleQhIso P n).hom) ≫ (homologyFunctor AddCommGrpCat.{v} n).map
          (R.map ((singleQhIso P n).inv ≫
            Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map φ))) =
        (homologyFunctor AddCommGrpCat.{v} n).map
            (Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
              ((F.mapHomologicalComplex (.up ℤ)).map φ))) ≫
          (homologyFunctor AddCommGrpCat.{v} n).map
            (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj J)) := by
      simp only [← Functor.map_comp, Category.assoc, ← R.map_comp, Iso.hom_inv_id_assoc]
      rw [Functor.mapHomotopyCategory_map] at hnat
      exact congrArg (homologyFunctor AddCommGrpCat.{v} n).map hnat.symm
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e1).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (homologyQhIso_inv_naturality n ((F.mapHomologicalComplex (.up ℤ)).map φ)))).trans
          (Category.assoc _ _ _)))
  have := ConcreteCategory.congr_hom key (unitClass F P p n)
  simp only [ConcreteCategory.comp_apply] at this
  exact this

variable (hP : ∀ M : A, Function.Bijective (fun f : P ⟶ M => F.map f p))
  (hβ : ∀ I : CochainComplex A ℤ, I.IsKInjective →
    IsIso (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj I)))
  (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
    J.IsKInjective ∧ QuasiIso q)

include hP hβ in
/-- **Corepresentability on a K-injective complex.** -/
theorem bijective_homologyFunctor_map_universalClass_of_isKInjective
    (J : CochainComplex A ℤ) [J.IsKInjective] :
    Function.Bijective (fun u : (singleFunctor A n).obj P ⟶
        Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj J) =>
      (homologyFunctor AddCommGrpCat.{v} n).map (R.map u) (universalClass F P p R β n)) := by
  have := hβ J inferInstance
  have hinj : Function.Injective ((homologyFunctor AddCommGrpCat.{v} n).map
      (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj J))) :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hinj' : Function.Injective (homologyQhIso n (mapComplex F J)).inv :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hsurj : ∀ u : (singleFunctor A n).obj P ⟶
      Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj J), ∃ φ : singleComplex P n ⟶ J,
        u = (singleQhIso P n).inv ≫ Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map φ) := by
    intro u
    obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective _ J).2
      ((singleQhIso P n).hom ≫ u)
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
    exact ⟨φ, by rw [hg, Iso.inv_hom_id_assoc]⟩
  refine ⟨fun u₁ u₂ h => ?_, fun y => ?_⟩
  · obtain ⟨φ₁, rfl⟩ := hsurj u₁
    obtain ⟨φ₂, rfl⟩ := hsurj u₂
    dsimp only at h
    rw [homologyFunctor_map_universalClass, homologyFunctor_map_universalClass] at h
    have h0 : classOf F P p n (φ₁ - φ₂) = 0 := by rw [classOf_sub, hinj' (hinj h), sub_self]
    have hq := quotient_map_eq_zero_of_classOf_eq_zero F P p n hP _ h0
    rw [Functor.map_sub, sub_eq_zero] at hq
    rw [hq]
  · obtain ⟨φ, hφ⟩ := exists_classOf_eq F P p n hP J ((homologyQhIso n (mapComplex F J)).hom
      (inv ((homologyFunctor AddCommGrpCat.{v} n).map
        (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj J))) y))
    refine ⟨(singleQhIso P n).inv ≫ Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map φ), ?_⟩
    dsimp only
    rw [homologyFunctor_map_universalClass, hφ]
    exact (congrArg _ (Iso.hom_inv_id_apply _ _)).trans (IsIso.inv_hom_id_apply _ _)

include hP hβ hres in
/-- **`H^n ∘ RF` is corepresented by `P[-n]`.** For every object `K` of `D(𝒜)`,
`Hom_{D(𝒜)}(P[-n], K) ⟶ H^n(RF(K))`, `u ↦ H^n(RF(u))(e)`, is bijective, where `e` is
`universalClass`, the class of `p`. -/
theorem bijective_homologyFunctor_map_universalClass (K : DerivedCategory A) :
    Function.Bijective (fun u : (singleFunctor A n).obj P ⟶ K =>
      (homologyFunctor AddCommGrpCat.{v} n).map (R.map u) (universalClass F P p R β n)) := by
  obtain ⟨J, q, hJ, hq⟩ := hres (Q.objPreimage K)
  have : IsIso (Q.map q) := (isIso_Q_map_iff_quasiIso (C := A) q).2 hq
  let ψ : K ≅ Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj J) :=
    (Q.objObjPreimageIso K).symm ≪≫ asIso (Q.map q) ≪≫ ((quotientCompQhIso A).app J).symm
  have hψ : Function.Bijective ((homologyFunctor AddCommGrpCat.{v} n).map (R.map ψ.inv)) :=
    ConcreteCategory.bijective_of_isIso _
  have hc : Function.Bijective (fun u : (singleFunctor A n).obj P ⟶ K => u ≫ ψ.hom) :=
    ⟨fun a b h => by simpa using congrArg (· ≫ ψ.inv) h, fun w => ⟨w ≫ ψ.inv, by simp⟩⟩
  convert hψ.comp
    ((bijective_homologyFunctor_map_universalClass_of_isKInjective F P p R β n hP hβ J).comp hc)
    using 1
  funext u
  have h : (homologyFunctor AddCommGrpCat.{v} n).map (R.map (u ≫ ψ.hom)) ≫
      (homologyFunctor AddCommGrpCat.{v} n).map (R.map ψ.inv) =
        (homologyFunctor AddCommGrpCat.{v} n).map (R.map u) := by
    simp only [← Functor.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (ConcreteCategory.congr_hom h (universalClass F P p R β n)).symm

include hP hβ hres in
/-- **`H^n ∘ RF` is corepresented by `P[-n]`**, in existential form: some element
`e ∈ H^n(RF(P[-n]))` makes `u ↦ H^n(RF(u))(e)` bijective on every `Hom_{D(𝒜)}(P[-n], K)`. -/
theorem exists_bijective_homologyFunctor_map_rightDerived :
    ∃ e : (homologyFunctor AddCommGrpCat.{v} n).obj (R.obj ((singleFunctor A n).obj P)),
      ∀ K : DerivedCategory A, Function.Bijective (fun u : (singleFunctor A n).obj P ⟶ K =>
        (homologyFunctor AddCommGrpCat.{v} n).map (R.map u) e) :=
  ⟨universalClass F P p R β n, bijective_homologyFunctor_map_universalClass F P p R β n hP hβ hres⟩

end Derived

end Stacks.DerivedFunctor
