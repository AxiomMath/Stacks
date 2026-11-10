module

public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.Perfect.Duality

/-!
# Duality for systems of perfect complexes

Let `A` be a ring and let `(Kₙ)` be a system of perfect objects of `D(A)` indexed by `ℕ`, with
derived colimit `K = hocolim Kₙ`. For every object `E` of `D(A)`, derived Hom out of `K` is a
derived inverse limit of the system `E ⊗_A^L Kₙᵛ` of derived tensor products with the duals of the
terms: `RHom_A(K, E) = R lim (E ⊗_A^L Kₙᵛ)`.

## Main definitions

* `StacksDraft.Perfect.unitObjectOverRing`: the tensor unit of `D(A)`, the ring `A` in degree
  zero.
* `StacksDraft.Perfect.derivedDualFunctor`: the contravariant derived-dual functor `RHom(-, A)`
  on `D(A)`.
* `StacksDraft.Perfect.dualTensorSystem`: the inverse system `E ⊗ᴸ Kₙᵛ` attached to a system
  `(Kₙ)` and an object `E`.
* `StacksDraft.Perfect.homFunctorOverRing`: derived Hom over `A` into a fixed object, as a
  contravariant functor of the first argument.

## Main results

* `StacksDraft.Perfect.exists_distinguished_derivedHom_overRing`: derived Hom over `A` carries a
  distinguished triangle in the first variable to the start of a distinguished triangle.
* `StacksDraft.Perfect.isDerivedLimit_derivedHom_of_isHomotopyColimit`: derived Hom out of a
  homotopy colimit of perfect objects is a derived limit of the dual tensor system.

## Implementation notes

Equality with `R lim` is expressed invariantly through
`CategoryTheory.Pretriangulated.IsDerivedLimit`, since a derived limit is determined only up to
non-unique isomorphism. Derived tensor product and derived Hom are the fixed canonical adjunction
of [stacks 0A63], read over the ring itself through `derivedHomAdjunctionOverRing`; the tensor
unit is the ring in degree zero. The identification of `E ⊗ᴸ Kₙᵛ` with `RHom(Kₙ, E)` is the
tensor--Hom comparison of [stacks 07VI], which holds because each `Kₙ` is perfect.

## References

* [Stacks Project, Tag 0BKB](https://stacks.math.columbia.edu/tag/0BKB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StacksDraft.DerivedHom.Model (homComplexFunctorFlip)

universe u v w

namespace StacksDraft.Perfect

open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]
  [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]

/-- The tensor unit in `D(A)`, represented by `A` concentrated in degree zero. -/
public noncomputable abbrev unitObjectOverRing :
    DerivedCategory (ModuleCat.{max u v} A) :=
  (derivedScalarEquivalence.{u, v, w} A).functor.obj
    (unitObject (R := A))

/-- The contravariant derived-dual functor `RHomₐ(-, A)` on `D(A)`. -/
noncomputable def derivedDualFunctor :
    (DerivedCategory (ModuleCat.{max u v} A))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{max u v} A) :=
  Functor.prod' (Functor.id _) ((Functor.const _).obj (unitObjectOverRing A)) ⋙
    (derivedHomAdjunctionOverRing A).hom

/-- For a system `Kₙ` in `D(A)` and `E ∈ D(A)`, the inverse system whose `n`-th term is
`E ⊗ᴸ Kₙᵛ`, with transition maps induced contravariantly by derived duality. -/
noncomputable def dualTensorSystem
    (K : ℕ ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (E : DerivedCategory (ModuleCat.{max u v} A)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{max u v} A) :=
  Functor.prod' ((Functor.const _).obj E) (K.op ⋙ derivedDualFunctor A) ⋙
    (derivedHomAdjunctionOverRing A).tensor

section Proof

set_option backward.isDefEq.respectTransparency false
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

open CochainComplex HomComplex

private lemma homComplexFunctor_map_v (R : Type u) [CommRing R]
    (I X Y : CochainComplex (ModuleCat.{u} R) ℤ) (f : X ⟶ Y) (n : ℤ)
    (z : Cochain Y I n) (p q : ℤ) (hpq : p + n = q) :
    (((homComplexFunctorFlip R I).map f.op).f n z).v p q hpq =
      f.f p ≫ z.v p q hpq := by
  change (((Cochain.ofHom f).comp z (zero_add n)).comp
    (Cochain.ofHom (𝟙 I)) (add_zero n)).v p q hpq = _
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, HomologicalComplex.id_f, Category.comp_id]

/-- Transporting the middle and last vertices of a distinguished triangle `X → Y → Y → X⟦1⟧` along
an isomorphism `Y ≅ P` yields a distinguished triangle `X → P → P → X⟦1⟧`. -/
private lemma exists_distinguished_comp_iso
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y P : C} (p : X ⟶ Y) (f : Y ⟶ Y) (δ : Y ⟶ X⟦(1 : ℤ)⟧)
    (hδ : Triangle.mk p f δ ∈ distTriang C) (e : Y ≅ P) (g : P ⟶ P)
    (hfg : f ≫ e.hom = e.hom ≫ g) :
    ∃ δ', Triangle.mk (p ≫ e.hom) g δ' ∈ distTriang C := by
  exact exists_distinguished_of_iso (p ≫ e.hom) g (Triangle.mk p f δ) hδ (Iso.refl _) e.symm e.symm
    (by simp) (by
      dsimp
      apply (cancel_mono e.hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Iso.inv_hom_id_assoc] using congrArg (e.inv ≫ ·) hfg.symm)

private lemma isDerivedLimit_of_natIso
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    {F G : ℕᵒᵖ ⥤ C}
    [HasProduct fun n : ℕ ↦ F.obj (Opposite.op n)]
    [HasProduct fun n : ℕ ↦ G.obj (Opposite.op n)]
    (c : F ≅ G) (K : C) (hK : IsDerivedLimit F K) : IsDerivedLimit G K := by
  let c' : Discrete.functor (fun n : ℕ ↦ F.obj (Opposite.op n)) ≅
      Discrete.functor (fun n : ℕ ↦ G.obj (Opposite.op n)) :=
    Discrete.natIso fun n ↦ c.app (Opposite.op n.as)
  let e := HasLimit.isoOfNatIso c'
  have he (n : ℕ) : e.hom ≫ Pi.π (fun n : ℕ ↦ G.obj (Opposite.op n)) n =
      Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n ≫ c.hom.app (Opposite.op n) :=
    HasLimit.isoOfNatIso_hom_π c' ⟨n⟩
  let b (J : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ J.obj (Opposite.op n)] :=
    Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ J.obj (Opposite.op n)) n -
      Pi.π (fun n : ℕ ↦ J.obj (Opposite.op n)) (n + 1) ≫
        J.map (homOfLE (Nat.le_succ n)).op
  have hb : b F ≫ e.hom = e.hom ≫ b G := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, b, Pi.lift_comp_π,
      Preadditive.comp_sub]
    rw [← Category.assoc e.hom, he, Category.assoc,
      ← c.hom.naturality (homOfLE (Nat.le_succ n)).op, ← Category.assoc, Pi.lift_comp_π,
      Preadditive.sub_comp, Category.assoc]
  obtain ⟨p, δ, hδ⟩ := hK
  obtain ⟨δ', hδ'⟩ := exists_distinguished_comp_iso p (b F) δ hδ e (b G) hb
  exact ⟨_, δ', hδ'⟩

private def homTranspose {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] (d : DerivedHomAdjunction R)
    (X Y E : DerivedCategory (ModuleCat.{v} R)) :
    (X ⟶ d.hom.obj (Opposite.op Y, E)) ≃+ (Y ⟶ d.hom.obj (Opposite.op X, E)) where
  toFun a := (d.homEquiv Y X E).symm ((d.tensorSwap Y X).hom ≫ d.homEquiv X Y E a)
  invFun a := (d.homEquiv X Y E).symm ((d.tensorSwap Y X).inv ≫ d.homEquiv Y X E a)
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by simp [Preadditive.comp_add]

private lemma homTranspose_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] (d : DerivedHomAdjunction R)
    (X E : DerivedCategory (ModuleCat.{v} R))
    {Y Y' : DerivedCategory (ModuleCat.{v} R)} (f : Y' ⟶ Y)
    (a : X ⟶ d.hom.obj (Opposite.op Y, E)) :
    homTranspose d X Y' E (a ≫ d.hom.map (f.op, 𝟙 E)) =
      f ≫ homTranspose d X Y E a := by
  apply (d.homEquiv Y' X E).injective
  change (d.homEquiv Y' X E)
    ((d.homEquiv Y' X E).symm ((d.tensorSwap Y' X).hom ≫
      d.homEquiv X Y' E (a ≫ d.hom.map (f.op, 𝟙 E)))) = _
  rw [AddEquiv.apply_symm_apply, d.homEquiv_dinaturality,
    d.homEquiv_naturality_left]
  change _ = d.tensor.map (show (Y', X) ⟶ (Y, X) from (f, 𝟙 X)) ≫
    d.homEquiv Y X E ((d.homEquiv Y X E).symm
      ((d.tensorSwap Y X).hom ≫ d.homEquiv X Y E a))
  rw [AddEquiv.apply_symm_apply]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ d.homEquiv X Y E a) (d.tensorSwap_naturality f (𝟙 X)).symm

private lemma derivedHom_additive {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] (d : DerivedHomAdjunction R)
    (E : DerivedCategory (ModuleCat.{v} R)) :
    ((CategoryTheory.Functor.curry.obj d.hom).flip.obj E).Additive where
  map_add {X Y} f g := by
    apply (homTranspose d (d.hom.obj (X, E)) Y.unop E).injective
    change homTranspose d _ Y.unop E
      (d.hom.map (show (X, E) ⟶ (Y, E) from (f + g, 𝟙 E))) =
      homTranspose d _ Y.unop E
        (d.hom.map (show (X, E) ⟶ (Y, E) from (f, 𝟙 E)) +
          d.hom.map (show (X, E) ⟶ (Y, E) from (g, 𝟙 E)))
    have hn (k : X ⟶ Y) := homTranspose_naturality d (d.hom.obj (X, E)) E k.unop (𝟙 _)
    simp only [Category.id_comp] at hn
    have h₁ := hn (f + g)
    have h₂ := hn f
    have h₃ := hn g
    change homTranspose d _ Y.unop E
      (d.hom.map (show (X, E) ⟶ (Y, E) from (f + g, 𝟙 E))) =
      (f + g).unop ≫ homTranspose d _ X.unop E (𝟙 _) at h₁
    change homTranspose d _ Y.unop E
      (d.hom.map (show (X, E) ⟶ (Y, E) from (f, 𝟙 E))) =
      f.unop ≫ homTranspose d _ X.unop E (𝟙 _) at h₂
    change homTranspose d _ Y.unop E
      (d.hom.map (show (X, E) ⟶ (Y, E) from (g, 𝟙 E))) =
      g.unop ≫ homTranspose d _ X.unop E (𝟙 _) at h₃
    rw [map_add, h₁, h₂, h₃, unop_add, Preadditive.add_comp]

private def derivedHomCoproductIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] (d : DerivedHomAdjunction R)
    {J : Type*} (K : J → DerivedCategory (ModuleCat.{v} R)) [HasCoproduct K]
    (E : DerivedCategory (ModuleCat.{v} R))
    [HasProduct fun j ↦ d.hom.obj (Opposite.op (K j), E)] :
    d.hom.obj (Opposite.op (∐ K), E) ≅ ∏ᶜ fun j ↦ d.hom.obj (Opposite.op (K j), E) where
  hom := Pi.lift fun j ↦ d.hom.map ((Sigma.ι K j).op, 𝟙 E)
  inv := (homTranspose d _ (∐ K) E).symm
    (Sigma.desc fun j ↦ homTranspose d _ (K j) E (Pi.π _ j))
  hom_inv_id := by
    apply (homTranspose d _ (∐ K) E).injective
    apply Sigma.hom_ext
    intro j
    rw [← homTranspose_naturality, Category.assoc, show (homTranspose d _ (∐ K) E).symm
        (Sigma.desc fun j ↦ homTranspose d _ (K j) E (Pi.π _ j)) ≫
        d.hom.map ((Sigma.ι K j).op, 𝟙 E) = Pi.π _ j by
      apply (homTranspose d _ (K j) E).injective
      rw [homTranspose_naturality, AddEquiv.apply_symm_apply, Sigma.ι_comp_desc], Pi.lift_comp_π]
    simpa only [Category.id_comp] using
      homTranspose_naturality d _ E (Sigma.ι K j) (𝟙 _)
  inv_hom_id := by
    apply Pi.hom_ext
    intro j
    rw [Category.assoc, Pi.lift_comp_π, Category.id_comp]
    apply (homTranspose d _ (K j) E).injective
    rw [homTranspose_naturality, AddEquiv.apply_symm_apply, Sigma.ι_comp_desc]

private lemma tensorHom_naturality_left {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))]
    {K K' : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))}
    (f : K' ⟶ K) (L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    let d := derivedHomData (R := R)
    d.tensor.map (𝟙 L, d.hom.map (f.op, 𝟙 (unitObject (R := R)))) ≫
        tensorDualHom K' L =
      tensorDualHom K L ≫ d.hom.map (f.op, 𝟙 L) := by
  dsimp only
  let d := derivedHomData (R := R)
  apply (d.homEquiv _ K' L).injective
  rw [d.homEquiv_naturality_left, d.homEquiv_dinaturality]
  dsimp only [tensorDualHom]
  simp only [d, AddEquiv.apply_symm_apply]
  rw [d.tensorAssoc_naturality_assoc]
  have h := d.tensorAssoc_naturality (𝟙 L) (𝟙 (derivedDual K)) f
  rw [d.tensor_map_id] at h
  rw [reassoc_of% h]
  simp only [← Category.assoc]
  congr 2
  have hv := congrArg (fun g ↦ d.tensor.map (show (L, d.tensor.obj
      (derivedDual K, K')) ⟶ (L, unitObject (R := R)) from (𝟙 L, g)))
    (d.evaluation_naturality_left (M := unitObject (R := R)) f)
  have hc₁ := d.tensor_map_comp (𝟙 L)
    (d.tensor.map (show (derivedDual K, K') ⟶
      (derivedDual K', K') from
        (d.hom.map (f.op, 𝟙 (unitObject (R := R))), 𝟙 K')))
    (𝟙 L) (d.evaluation K' (unitObject (R := R)))
  have hc₂ := d.tensor_map_comp (𝟙 L)
    (d.tensor.map (show (derivedDual K, K') ⟶
      (derivedDual K, K) from (𝟙 _, f)))
    (𝟙 L) (d.evaluation K (unitObject (R := R)))
  simp only [Category.comp_id] at hc₁ hc₂
  rw [← hc₁, ← hc₂] at hv
  simpa only [Category.assoc, d] using
    congrArg ((d.tensorAssoc L (derivedDual K) K').hom ≫ ·) hv

variable (A : Type u) [CommRing A]
  [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]

/-- Derived Hom over a ring in an independently chosen module universe, into a fixed second
argument, as a contravariant functor of the first. -/
public abbrev homFunctorOverRing
    (E : DerivedCategory (ModuleCat.{max u v} A)) :=
  (CategoryTheory.Functor.curry.obj (derivedHomAdjunctionOverRing A).hom).flip.obj E

private def restrictScalarsULiftEquiv (M : ModuleCat.{max u v} A) :
    LinearEquiv (R := A) (S := ULift.{v} A)
      (σ' := ↑(ULift.ringEquiv : ULift.{v} A ≃+* A))
      (↑(ULift.ringEquiv : ULift.{v} A ≃+* A).symm) M
      ((ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom).obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma isPerfect_inverse_scalarEquivalence
    (K : DerivedCategory (ModuleCat.{max u v} A)) (hK : IsPerfect K) :
    IsPerfect ((derivedScalarEquivalence.{u,v,w} A).inverse.obj K) := by
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨i⟩⟩ := hK
  let F := (uliftModuleEquivalence.{u,max u v,v} A).inverse
  let := ha
  let := hb
  refine ⟨(F.mapHomologicalComplex (.up ℤ)).obj P, a, b, inferInstance, inferInstance,
    ?_, ?_, ⟨?_⟩⟩
  · intro n
    let := hfin n
    exact Module.Finite.of_surjective (restrictScalarsULiftEquiv A (P.X n)).toLinearMap
      (restrictScalarsULiftEquiv A (P.X n)).surjective
  · intro n
    let := hproj n
    exact Module.Projective.of_equiv (restrictScalarsULiftEquiv A (P.X n))
  · exact (derivedScalarEquivalence A).inverse.mapIso i ≪≫
      F.mapDerivedCategoryFactors.app P

/-- Derived Hom over a ring in an independently chosen module universe carries a distinguished
triangle in the first variable to the start of a distinguished triangle. -/
public lemma exists_distinguished_derivedHom_overRing
    (E : DerivedCategory (ModuleCat.{max u v} A))
    (T : Triangle (DerivedCategory (ModuleCat.{max u v} A))) (hT : T ∈ distTriang _) :
    ∃ δ, Triangle.mk ((homFunctorOverRing A E).map T.mor₂.op)
      ((homFunctorOverRing A E).map T.mor₁.op) δ ∈ distTriang _ := by
  let e := derivedScalarEquivalence.{u,v,w} A
  let : e.inverse.CommShift ℤ := by
    dsimp [e, derivedScalarEquivalence, uliftDerivedEquivalence,
      Localization.equivalence, CategoryTheory.Equivalence.mk]
    infer_instance
  let : e.inverse.IsTriangulated := by
    dsimp [e, derivedScalarEquivalence, uliftDerivedEquivalence,
      Localization.equivalence, CategoryTheory.Equivalence.mk]
    infer_instance
  let : e.functor.CommShift ℤ := by
    dsimp [e, derivedScalarEquivalence, uliftDerivedEquivalence,
      Localization.equivalence, CategoryTheory.Equivalence.mk]
    infer_instance
  let : e.functor.IsTriangulated := by
    dsimp [e, derivedScalarEquivalence, uliftDerivedEquivalence,
      Localization.equivalence, CategoryTheory.Equivalence.mk]
    infer_instance
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedHom
    (derivedHomAdjunctionULift (R := A)) (e.inverse.obj E)
    (e.inverse.mapTriangle.obj T) (e.inverse.map_distinguished T hT)
  refine ⟨e.functor.map δ ≫ (e.functor.commShiftIso (1 : ℤ)).hom.app _, ?_⟩
  convert e.functor.map_distinguished _ hδ using 1
  dsimp [homFunctorOverRing, derivedHomAdjunctionOverRing,
    DerivedHomAdjunction.transport, DerivedHomAdjunction.transportHom,
    derivedHomFunctor]
  simp only [CategoryTheory.Functor.map_id]
  rfl

private lemma isDerivedLimit_hom_of_isHomotopyColimit
    (Ksys : ℕ ⥤ DerivedCategory (ModuleCat.{max u v} A)) [HasCoproduct Ksys.obj]
    (K E : DerivedCategory (ModuleCat.{max u v} A)) (hK : IsHomotopyColimit Ksys K)
    [hprod : HasProduct fun n : ℕ ↦ (Ksys.op ⋙ homFunctorOverRing A E).obj (Opposite.op n)] :
    IsDerivedLimit (Ksys.op ⋙ homFunctorOverRing A E)
      ((homFunctorOverRing A E).obj (Opposite.op K)) := by
  let H := homFunctorOverRing A E
  let := derivedHom_additive (derivedHomAdjunctionOverRing A) E
  obtain ⟨p, q, hT⟩ := hK
  let d := Sigma.desc fun n ↦ Sigma.ι Ksys.obj n -
    Ksys.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι Ksys.obj (n + 1)
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedHom_overRing A E (Triangle.mk d p q) hT
  let : HasProduct fun n : ℕ ↦ (derivedHomAdjunctionOverRing A).hom.obj
      (Opposite.op (Ksys.obj n), E) := hprod
  let e := derivedHomCoproductIso (derivedHomAdjunctionOverRing A) Ksys.obj E
  let D := Ksys.op ⋙ H
  let : HasProduct fun n : ℕ ↦ D.obj (Opposite.op n) := hprod
  let b := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ D.obj (Opposite.op n)) n -
    Pi.π (fun n : ℕ ↦ D.obj (Opposite.op n)) (n + 1) ≫
      D.map (homOfLE (Nat.le_succ n)).op
  have he (n : ℕ) : e.hom ≫ Pi.π (fun n : ℕ ↦ D.obj (Opposite.op n)) n =
      H.map (Sigma.ι Ksys.obj n).op := by
    change Pi.lift _ ≫ Pi.π _ n = _
    exact Pi.lift_comp_π _ _
  have hb : H.map d.op ≫ e.hom = e.hom ≫ b := by
    apply Pi.hom_ext
    intro n
    change (H.map d.op ≫ e.hom) ≫ Pi.π (fun n : ℕ ↦ D.obj (Opposite.op n)) n =
      (e.hom ≫ b) ≫ Pi.π (fun n : ℕ ↦ D.obj (Opposite.op n)) n
    rw [Category.assoc, he, ← H.map_comp, ← op_comp]
    dsimp only [d]
    rw [Sigma.ι_comp_desc, op_sub, op_comp, H.map_sub, H.map_comp]
    simp only [b, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, he]
    rw [← Category.assoc, he]
    rfl
  obtain ⟨δ', hδ'⟩ := exists_distinguished_comp_iso (H.map p.op) (H.map d.op) δ hδ e b hb
  exact ⟨_, δ', hδ'⟩

private def dualTensorSystemIso
    (Ksys : ℕ ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (hperfect : ∀ n : ℕ, IsPerfect (Ksys.obj n))
    (E : DerivedCategory (ModuleCat.{max u v} A)) :
    dualTensorSystem A Ksys E ≅ Ksys.op ⋙ homFunctorOverRing A E := by
  let e := derivedScalarEquivalence.{u,v,w} A
  let d := derivedHomData (R := A)
  let U := unitObject (R := A)
  let B := Ksys.op ⋙ e.inverse.op
  let V := B ⋙ derivedHomFunctor d (e.inverse.obj (e.functor.obj U))
  let W := B ⋙ derivedHomFunctor d U
  let cU : V ≅ W := B.isoWhiskerLeft
    ((CategoryTheory.Functor.curry.obj d.hom).flip.mapIso (e.unitIso.app U).symm)
  let cV : V ⋙ e.functor ⋙ e.inverse ≅ W :=
    V.isoWhiskerLeft e.unitIso.symm ≪≫ Functor.rightUnitor V ≪≫ cU
  let cE : (Functor.const ℕᵒᵖ).obj E ⋙ e.inverse ≅
      (Functor.const ℕᵒᵖ).obj (e.inverse.obj E) :=
    ((Functor.compConstIso ℕᵒᵖ e.inverse).app E).symm
  let S := Functor.prod' ((Functor.const ℕᵒᵖ).obj (e.inverse.obj E)) W ⋙ d.tensor
  let c₁ : dualTensorSystem A Ksys E ≅
      Functor.prod' ((Functor.const ℕᵒᵖ).obj E ⋙ e.inverse)
        (V ⋙ e.functor ⋙ e.inverse) ⋙ d.tensor ⋙ e.functor :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro n m f
      dsimp [dualTensorSystem, derivedDualFunctor, derivedHomAdjunctionOverRing,
        DerivedHomAdjunction.transport,
        DerivedHomAdjunction.transportTensor,
        DerivedHomAdjunction.transportHom, V, B, derivedHomFunctor]
      simp only [Category.comp_id, Category.id_comp, CategoryTheory.Functor.map_id]
      rfl)
  let c₂ : Functor.prod' ((Functor.const ℕᵒᵖ).obj E ⋙ e.inverse)
        (V ⋙ e.functor ⋙ e.inverse) ⋙ d.tensor ⋙ e.functor ≅ S ⋙ e.functor :=
    CategoryTheory.Functor.isoWhiskerRight ((prodFunctorToFunctorProd _ _ _).mapIso (cE.prod cV))
      (d.tensor ⋙ e.functor)
  let c₃ : S ≅ B ⋙ derivedHomFunctor d (e.inverse.obj E) :=
    NatIso.ofComponents (fun n ↦ by
      let := (isPerfect_derivedDual_and_naturalIsos
        (e.inverse.obj (Ksys.obj n.unop))
        (isPerfect_inverse_scalarEquivalence A _ (hperfect n.unop))).tensorDualHom_isIso
          (e.inverse.obj E)
      exact asIso (tensorDualHom (e.inverse.obj (Ksys.obj n.unop))
        (e.inverse.obj E))) (by
      intro n m f
      exact tensorHom_naturality_left (e.inverse.map (Ksys.map f.unop)) (e.inverse.obj E))
  let c₄ : (B ⋙ derivedHomFunctor d (e.inverse.obj E)) ⋙ e.functor ≅
      Ksys.op ⋙ homFunctorOverRing A E :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro n m f
      dsimp [homFunctorOverRing, derivedHomAdjunctionOverRing,
        DerivedHomAdjunction.transport,
        DerivedHomAdjunction.transportHom, B, derivedHomFunctor]
      simp only [Category.comp_id, Category.id_comp, CategoryTheory.Functor.map_id]
      rfl)
  exact c₁ ≪≫ c₂ ≪≫ CategoryTheory.Functor.isoWhiskerRight c₃ e.functor ≪≫ c₄

end Proof

/-- If `K` is a homotopy colimit of a sequential system of perfect derived
objects `Kₙ`, then `RHomₐ(K, E)` is a derived inverse limit of the inverse system
`E ⊗ᴸ Kₙᵛ`. -/
@[stacks 0BKB]
theorem isDerivedLimit_derivedHom_of_isHomotopyColimit
    (Ksys : ℕ ⥤ DerivedCategory (ModuleCat.{max u v} A)) [HasCoproduct Ksys.obj]
    (hperfect : ∀ n : ℕ, IsPerfect (Ksys.obj n))
    (K E : DerivedCategory (ModuleCat.{max u v} A)) (hK : IsHomotopyColimit Ksys K)
    [HasProduct fun n : ℕ ↦ (dualTensorSystem A Ksys E).obj (Opposite.op n)] :
    IsDerivedLimit (dualTensorSystem A Ksys E)
      ((derivedHomAdjunctionOverRing A).hom.obj (Opposite.op K, E)) := by
  let c := dualTensorSystemIso A Ksys hperfect E
  let c' : Discrete.functor (fun n : ℕ ↦ (dualTensorSystem A Ksys E).obj (Opposite.op n)) ≅
      Discrete.functor (fun n : ℕ ↦
        (Ksys.op ⋙ homFunctorOverRing A E).obj (Opposite.op n)) :=
    Discrete.natIso fun n ↦ c.app (Opposite.op n.as)
  let := hasLimit_of_iso c'
  exact isDerivedLimit_of_natIso c.symm _
    (isDerivedLimit_hom_of_isHomotopyColimit A Ksys K E hK)

end StacksDraft.Perfect

end
