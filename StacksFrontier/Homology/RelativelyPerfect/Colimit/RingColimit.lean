module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit.ExtensionScalars
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.ExtensionScalars

/-!
# Elements over a filtered colimit of rings

Preservation of exact colimits by homology, and descent of elements, finite families of
elements and their relations, and finite presentation along the stages of a filtered colimit of
`R₀`-algebras and of their base changes `Rᵢ ⊗[R₀] A₀`.

This is part 2 of 10 of `StacksFrontier.Homology.RelativelyPerfect.Colimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open CochainComplex.DerivedExtensionScalars
open StacksDraft.TorAmplitude
open scoped TensorProduct

open Stacks.HomologyColimit

namespace PseudoCoherence

open StacksDraft.RelativelyPerfect (finite_homCochain_support homCochainBaseChange
    homCochainBaseChange_bijective homCochainBaseChange_tmul homCochainExtendScalars
    homCochainRestrict homComplexBaseChange linearMap_isBaseChange_of_finiteFree)

universe uI uJ uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] CochainComplex.DerivedTensor.instAdditiveModuleCatExtensionScalars
  CochainComplex.DerivedTensor.instIsLeftAdjointModuleCatExtensionScalars

section HomologyColimits

variable {C : Type*} [Category* C] [Abelian C] {J : Type*} [Category* J]

/-- Homology of short complexes preserves colimits of every exact shape. -/
public theorem preservesColimitsOfShape_shortComplex_homologyFunctor
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor C) :=
  Stacks.HomologyColimit.preservesColimitsOfShape_shortComplex_homologyFunctor (A := C) (J := J)

/-- Homology commutes with colimits whenever colimits of that shape are exact. -/
public theorem preservesColimitsOfShape_homologyFunctor
    {ι : Type*} (c : ComplexShape ι) [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] (i : ι) :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor C c i) :=
  Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (A := C) (J := J) c i

end HomologyColimits

/-- The comparison map from a directed colimit of algebras is bijective as soon as every element
of the target comes from a stage and every element of a stage that vanishes in the target already
vanishes at a later stage. This is the form in which the 05N7 hypothesis is verified. -/
private theorem directLimit_algebra_lift_bijective.{w, u, v}
    {J : Type w} [Preorder J] [Nonempty J] [IsDirectedOrder J] {A : Type u} [CommRing A]
    {S : J → Type v} [∀ j, CommRing (S j)] [∀ j, Algebra A (S j)]
    (f : ∀ i j, i ≤ j → S i →ₐ[A] S j) [DirectedSystem S fun i j h ↦ ⇑(f i j h)]
    {R : Type*} [CommRing R] [Algebra A R] (g : ∀ j, S j →ₐ[A] R)
    (hf : ∀ i j (h : i ≤ j) (x : S i), g j (f i j h x) = g i x)
    (hsurj : ∀ r : R, ∃ (j : J) (s : S j), g j s = r)
    (hinj : ∀ (j : J) (s : S j), g j s = 0 → ∃ (k : J) (hjk : j ≤ k), f j k hjk s = 0) :
    Function.Bijective (DirectLimit.Algebra.lift S f R g hf) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun r ↦ ?_⟩
  · induction x using DirectLimit.induction with
    | ih i s =>
      have hs : g i s = 0 := by
        rw [← DirectLimit.Algebra.lift_of (G := S) (f := f) R g hf i s]
        exact hx
      obtain ⟨k, hik, hk⟩ := hinj i s hs
      show DirectLimit.Algebra.of S f i s = 0
      rw [← DirectLimit.Algebra.of_f (hij := hik), hk, map_zero]
  · obtain ⟨j, s, rfl⟩ := hsurj r
    exact ⟨DirectLimit.Algebra.of S f j s,
      DirectLimit.Algebra.lift_of (G := S) (f := f) R g hf j s⟩

/-- A filtered category with independently sized objects and morphisms has a directed
partially ordered final model. -/
private theorem exists_directed_final (I : Type uI) [Category.{uJ} I] [IsFiltered I] :
    ∃ (J : Type (max uI uJ)) (_ : PartialOrder J) (_ : IsDirected J (· ≤ ·))
      (_ : Nonempty J) (G : J ⥤ I), G.Final := by
  let e : I ≌ AsSmall.{0} I := AsSmall.equiv
  have : IsFiltered (AsSmall.{0} I) := IsFiltered.of_equivalence e
  obtain ⟨J, _, _, _, G, _⟩ := IsFiltered.exists_directed (AsSmall.{0} I)
  exact ⟨J, inferInstance, inferInstance, inferInstance, G ⋙ e.inverse, inferInstance⟩

/-- Forgetting the algebra structure preserves a connected colimit, without any relation
between the universe of the base ring and the universe of its algebras. -/
private def isColimit_forget₂_commAlgCat
    {R : Type*} [CommRing R] {J : Type*} [Category* J] [IsConnected J]
    {F : J ⥤ CommAlgCat.{uR} R} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{uR} R) CommRingCat).mapCocone c) := by
  classical
  refine IsColimit.ofExistsUnique fun s ↦ ?_
  obtain ⟨a, ha⟩ := constant_of_preserves_morphisms' (α := R →+* s.pt)
    (fun j ↦ (s.ι.app j).hom.comp (algebraMap R (F.obj j))) (by
      intro i j f
      ext r
      change (s.ι.app i).hom (algebraMap R (F.obj i) r) =
        (s.ι.app j).hom (algebraMap R (F.obj j) r)
      have hw := congrArg (fun q ↦ q.hom (algebraMap R (F.obj i) r)) (s.w f)
      simpa using hw.symm)
  let : Algebra R s.pt := a.toAlgebra
  let s' : Cocone F :=
    { pt := CommAlgCat.of R s.pt
      ι :=
        { app := fun j ↦ CommAlgCat.ofHom
            { __ := (s.ι.app j).hom
              commutes' := fun r ↦ RingHom.congr_fun (ha j) r }
          naturality := fun i j f ↦ by
            ext x
            exact congrArg (fun q ↦ q.hom x) (s.w f) } }
  refine ⟨CommRingCat.ofHom (hc.desc s').hom.toRingHom, ?_, ?_⟩
  · intro j
    ext x
    exact congrArg (fun q ↦ q.hom x) (hc.fac s' j)
  · intro m hm
    let m' : c.pt ⟶ s'.pt := CommAlgCat.ofHom
      { __ := m.hom
        commutes' := fun r ↦ by
          let j : J := Classical.arbitrary J
          change m.hom (algebraMap R c.pt r) = a r
          calc
            _ = m.hom ((c.ι.app j).hom (algebraMap R (F.obj j) r)) := by
              rw [AlgHom.commutes]
              rfl
            _ = (s.ι.app j).hom (algebraMap R (F.obj j) r) :=
              congrArg (fun q ↦ q.hom (algebraMap R (F.obj j) r)) (hm j)
            _ = a r := RingHom.congr_fun (ha j) r }
    have he : m' = hc.desc s' := hc.uniq s' m' (fun j ↦ by
      ext x
      exact congrArg (fun q ↦ q.hom x) (hm j))
    exact congrArg (fun q ↦ CommRingCat.ofHom q.hom.toRingHom) he

/-- The lifted ring-colimit hypothesis also describes the colimit of underlying sets. -/
private def isColimit_underlying_ulift {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c)) :
    IsColimit ((forget (CommAlgCat.{max uI uJ uR} R₀)).mapCocone
      ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c)) := by
  have : IsConnected I := IsFiltered.isConnected I
  have : PreservesFilteredColimitsOfSize.{uJ, uI}
      (forget CommRingCat.{max uI uJ uR}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max uI uJ uR, max uI uJ uR} _
  exact isColimitOfPreserves (forget CommRingCat.{max uI uJ uR})
    (isColimit_forget₂_commAlgCat hc)

/-- Every element of the colimit ring comes from a stage, even for large index categories. -/
private theorem exists_stage_element {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (x : c.pt) : ∃ i y, (c.ι.app i).hom y = x := by
  obtain ⟨i, y, hy⟩ := Types.jointly_surjective _ (isColimit_underlying_ulift hc) (ULift.up x)
  exact ⟨i, y.down, congrArg ULift.down hy⟩

/-- Equality in the colimit ring holds at a common later stage. -/
private theorem stage_elements_eq_iff {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    {i j : I} (x : F.obj i) (y : F.obj j) :
    (c.ι.app i).hom x = (c.ι.app j).hom y ↔
      ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k), (F.map f).hom x = (F.map g).hom y := by
  have h := Types.FilteredColimit.isColimit_eq_iff _ (isColimit_underlying_ulift hc)
    (xi := ULift.up x) (xj := ULift.up y)
  change (ULift.up ((c.ι.app i).hom x) : ULift.{max uI uJ} c.pt) =
      ULift.up ((c.ι.app j).hom y) ↔
    ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k),
      (ULift.up ((F.map f).hom x) : ULift.{max uI uJ} (F.obj k)) =
        ULift.up ((F.map g).hom y) at h
  simpa only [ULift.up.injEq] using h

/-- A finite family of elements of the colimit ring descends to one stage. -/
private theorem exists_stage_finite_family {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    {σ : Type*} [Finite σ] (x : σ → c.pt) :
    ∃ (i : I) (y : σ → F.obj i), ∀ a, (c.ι.app i).hom (y a) = x a := by
  classical
  let := Fintype.ofFinite σ
  choose i y hy using fun a ↦ exists_stage_element hc (x a)
  let s := IsFiltered.cocone (Discrete.functor i)
  refine ⟨s.pt, fun a ↦ (F.map (s.ι.app ⟨a⟩)).hom (y a), fun a ↦ ?_⟩
  have hw := congrArg (fun q ↦ q.hom (y a)) (c.w (s.ι.app ⟨a⟩))
  exact hw.trans (hy a)

/-- Equality between two elements from one stage holds after one further transition. -/
private theorem stage_elements_eq_iff' {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    {i : I} (x y : F.obj i) :
    (c.ι.app i).hom x = (c.ι.app i).hom y ↔
      ∃ (j : I) (f : i ⟶ j), (F.map f).hom x = (F.map f).hom y := by
  have h := Types.FilteredColimit.isColimit_eq_iff' (isColimit_underlying_ulift hc)
    (ULift.up x) (ULift.up y)
  change (ULift.up ((c.ι.app i).hom x) : ULift.{max uI uJ} c.pt) =
      ULift.up ((c.ι.app i).hom y) ↔
    ∃ (j : I) (f : i ⟶ j),
      (ULift.up ((F.map f).hom x) : ULift.{max uI uJ} (F.obj j)) =
        ULift.up ((F.map f).hom y) at h
  simpa only [ULift.up.injEq] using h

/-- A finite family of equalities in the colimit holds after one transition. -/
private theorem exists_stage_finite_equalities {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    {σ : Type*} [Finite σ] {i : I} (x y : σ → F.obj i)
    (h : ∀ a, (c.ι.app i).hom (x a) = (c.ι.app i).hom (y a)) :
    ∃ (j : I) (f : i ⟶ j), ∀ a, (F.map f).hom (x a) = (F.map f).hom (y a) := by
  classical
  let := Fintype.ofFinite σ
  choose j f hf using fun a ↦ (stage_elements_eq_iff' hc (x a) (y a)).mp (h a)
  let s := IsFiltered.cocone (Discrete.functor fun a ↦ Under.mk (f a))
  refine ⟨s.pt.right, s.pt.hom, fun a ↦ ?_⟩
  have hw : f a ≫ (s.ι.app ⟨a⟩).right = s.pt.hom := Under.w (s.ι.app ⟨a⟩)
  rw [← hw, F.map_comp]
  exact congrArg (fun z ↦ (F.map (s.ι.app ⟨a⟩).right).hom z) (hf a)

/-- The colimit ring has its universal mapping property against rings in any universe. -/
private theorem existsUnique_ringHom_desc {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    {S : Type*} [CommRing S] (ρ : ∀ i, F.obj i →+* S)
    (hρ : ∀ {i j} (f : i ⟶ j), (ρ j).comp (F.map f).hom.toRingHom = ρ i) :
    ∃! φ : c.pt →+* S, ∀ i, φ.comp (c.ι.app i).hom.toRingHom = ρ i := by
  classical
  choose j y hy using exists_stage_element hc
  let lift : c.pt → S := fun x ↦ ρ (j x) (y x)
  have fac (i : I) (x : F.obj i) : lift ((c.ι.app i).hom x) = ρ i x := by
    let z := (c.ι.app i).hom x
    obtain ⟨k, f, g, hfg⟩ := (stage_elements_eq_iff hc (y z) x).mp (hy z)
    show ρ (j z) (y z) = ρ i x
    calc
      _ = ρ k ((F.map f).hom (y z)) := (RingHom.congr_fun (hρ f) (y z)).symm
      _ = ρ k ((F.map g).hom x) := congrArg (ρ k) hfg
      _ = ρ i x := RingHom.congr_fun (hρ g) x
  have pair (x y : c.pt) :
      ∃ (i : I) (a b : F.obj i), (c.ι.app i).hom a = x ∧ (c.ι.app i).hom b = y := by
    obtain ⟨i, z, hz⟩ := exists_stage_finite_family hc (fun t : Bool ↦ cond t x y)
    exact ⟨i, z true, z false, hz true, hz false⟩
  let φ : c.pt →+* S :=
    { toFun := lift
      map_one' := by
        let i : I := Classical.choice IsFiltered.nonempty
        simpa only [map_one] using fac i 1
      map_mul' := fun x y ↦ by
        obtain ⟨i, a, b, rfl, rfl⟩ := pair x y
        rw [← map_mul, fac, fac, fac, map_mul]
      map_zero' := by
        let i : I := Classical.choice IsFiltered.nonempty
        simpa only [map_zero] using fac i 0
      map_add' := fun x y ↦ by
        obtain ⟨i, a, b, rfl, rfl⟩ := pair x y
        rw [← map_add, fac, fac, fac, map_add] }
  refine ⟨φ, (fun i ↦ RingHom.ext (fac i)), ?_⟩
  intro ψ hψ
  ext x
  obtain ⟨i, a, rfl⟩ := exists_stage_element hc x
  exact (RingHom.congr_fun (hψ i) a).trans (fac i a).symm

/-- The colimit algebra has its universal mapping property against algebras in any universe. -/
private theorem existsUnique_algHom_desc {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    {S : Type*} [CommRing S] [Algebra R₀ S] (ρ : ∀ i, F.obj i →ₐ[R₀] S)
    (hρ : ∀ {i j} (f : i ⟶ j), (ρ j).comp (F.map f).hom = ρ i) :
    ∃! φ : c.pt →ₐ[R₀] S, ∀ i, φ.comp (c.ι.app i).hom = ρ i := by
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_ringHom_desc hc (fun i ↦ (ρ i).toRingHom)
    (fun f ↦ congrArg AlgHom.toRingHom (hρ f))
  let ψ : c.pt →ₐ[R₀] S :=
    { __ := φ
      commutes' := fun r ↦ by
        let i : I := Classical.choice IsFiltered.nonempty
        calc
          φ (algebraMap R₀ c.pt r) = φ ((c.ι.app i).hom (algebraMap R₀ (F.obj i) r)) :=
            congrArg φ ((c.ι.app i).hom.commutes r).symm
          _ = ρ i (algebraMap R₀ (F.obj i) r) :=
            RingHom.congr_fun (hφ i) _
          _ = algebraMap R₀ S r := (ρ i).commutes r }
  refine ⟨ψ, (fun i ↦ AlgHom.ext (RingHom.congr_fun (hφ i))), ?_⟩
  intro ψ' hψ'
  apply AlgHom.coe_ringHom_injective
  exact huniq ψ'.toRingHom (fun i ↦ congrArg AlgHom.toRingHom (hψ' i))

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring the colimit of rings with the starting algebra gives its canonical colimit
in the category of algebras under that algebra. -/
private def isColimit_stageUnderCocone {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] :
    IsColimit (stageUnderCocone c A₀) := by
  classical
  refine IsColimit.ofExistsUnique fun s ↦ ?_
  dsimp only [stageUnderFunctor] at s
  let α : A₀ →+* s.pt.right :=
    s.pt.hom.hom.comp (ULift.ringEquiv.symm : A₀ ≃+* ULift.{uR} A₀).toRingHom
  let : Algebra R₀ s.pt.right := (α.comp (algebraMap R₀ A₀)).toAlgebra
  let α' : A₀ →ₐ[R₀] s.pt.right := { __ := α, commutes' := fun _ ↦ rfl }
  have right (i : I) (a : A₀) :
      (s.ι.app i).right.hom (1 ⊗ₜ[R₀] a) = α a :=
    congrArg (fun q ↦ q.hom (ULift.up a)) (Under.w (s.ι.app i))
  let ρ (i : I) : F.obj i →ₐ[R₀] s.pt.right :=
    { __ := (s.ι.app i).right.hom.comp Algebra.TensorProduct.includeLeftRingHom
      commutes' := fun r ↦ by
        change (s.ι.app i).right.hom
          (Algebra.TensorProduct.includeLeftRingHom (algebraMap R₀ (F.obj i) r)) = _
        exact (congrArg (s.ι.app i).right.hom
          (RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
            (R := R₀) (A := F.obj i) (B := A₀)) r)).trans
          (right i (algebraMap R₀ A₀ r)) }
  obtain ⟨ψ, hψ, _⟩ := existsUnique_algHom_desc hc ρ (fun {i j} f ↦ by
    ext x
    have hw := congrArg (fun q ↦ q.right.hom (x ⊗ₜ[R₀] (1 : A₀))) (s.w f)
    simpa [ρ, stageUnderFunctor, stageMap, Algebra.TensorProduct.map_tmul] using hw)
  let Φ := Algebra.TensorProduct.lift ψ α' (fun _ _ ↦ Commute.all _ _)
  have hΦ (i : I) (a : F.obj i) : Φ ((c.ι.app i).hom a ⊗ₜ[R₀] (1 : A₀)) =
      (s.ι.app i).right.hom (a ⊗ₜ[R₀] (1 : A₀)) := by
    have h := AlgHom.congr_fun (hψ i) a
    change ψ ((c.ι.app i).hom a) = (s.ι.app i).right.hom (a ⊗ₜ[R₀] (1 : A₀)) at h
    simpa [Φ] using h
  let m : (stageUnderCocone c A₀).pt ⟶ s.pt :=
    Under.homMk (CommRingCat.ofHom Φ.toRingHom) (by
      ext a
      simp [Φ, α', α, stageUnderCocone, baseToLimitMap,
        Algebra.TensorProduct.includeRight_apply])
  refine ⟨m, ?_, ?_⟩
  · intro i
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    change Φ.toRingHom.comp (stageToLimitMap c A₀ i) = (s.ι.app i).right.hom
    ext x
    · change Φ ((c.ι.app i).hom x ⊗ₜ[R₀] (1 : A₀)) = _
      exact hΦ i x
    · refine Eq.trans ?_ (right i x).symm
      change Φ ((c.ι.app i).hom 1 ⊗ₜ[R₀] x) = α x
      erw [Algebra.TensorProduct.lift_tmul, map_one (c.ι.app i).hom, map_one ψ, one_mul] <;> rfl
  · intro n hn
    dsimp only [stageUnderCocone] at n
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    change n.right.hom = Φ.toRingHom
    apply Algebra.TensorProduct.ringHom_ext (R := R₀) (A := c.pt) (B := A₀) <;>
      apply RingHom.ext <;> intro x
    · obtain ⟨i, a, rfl⟩ := exists_stage_element hc x
      have hw := congrArg (fun q ↦ q.right.hom (a ⊗ₜ[R₀] (1 : A₀))) (hn i)
      have hw' : n.right.hom ((c.ι.app i).hom a ⊗ₜ[R₀] (1 : A₀)) =
          (s.ι.app i).right.hom (a ⊗ₜ[R₀] (1 : A₀)) := by
        have he : stageToLimitMap c A₀ i (a ⊗ₜ[R₀] (1 : A₀)) =
            (c.ι.app i).hom a ⊗ₜ[R₀] (1 : A₀) := by
          simp [stageToLimitMap, Algebra.TensorProduct.map_tmul]
        exact (congrArg n.right.hom he).symm.trans hw
      exact hw'.trans (hΦ i a).symm
    · have hw := congrArg (fun q ↦ q.hom (ULift.up x)) (Under.w n)
      change n.right.hom (1 ⊗ₜ[R₀] x) = Φ (1 ⊗ₜ[R₀] x)
      calc
        _ = α x := hw
        _ = Φ (1 ⊗ₜ[R₀] x) := by simp [Φ, α']

/-- The transition maps are compatible with the maps to the limit algebra. -/
private theorem stageToLimitMap_comp_stageMap {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] {F : I ⥤ CommAlgCat.{uR} R₀} (c : Cocone F)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] {i j : I} (f : i ⟶ j)
    (y : stageAlgebra F A₀ i) :
    stageToLimitMap c A₀ j (stageMap F A₀ f y) = stageToLimitMap c A₀ i y := by
  have : (stageToLimitMap c A₀ j).comp (stageMap F A₀ f) = stageToLimitMap c A₀ i := by
    ext x
    all_goals simp [stageToLimitMap, stageMap]
  exact RingHom.congr_fun this y

/-- Every element of `R ⊗[R₀] A₀` comes from a stage. -/
private theorem exists_stage_tensor_element {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    (c : Cocone F) (hc : ∀ x : c.pt, ∃ i y, (c.ι.app i).hom y = x)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] (x : c.pt ⊗[R₀] A₀) :
    ∃ (i : I) (y : stageAlgebra F A₀ i), stageToLimitMap c A₀ i y = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨(IsFiltered.nonempty (C := I)).some, 0, map_zero _⟩
  | tmul x a =>
    obtain ⟨i, y, hy⟩ := hc x
    exact ⟨i, y ⊗ₜ a, by simp [stageToLimitMap, Algebra.TensorProduct.map_tmul, hy]⟩
  | add x z hx hz =>
    obtain ⟨i, y, rfl⟩ := hx
    obtain ⟨j, w, rfl⟩ := hz
    refine ⟨IsFiltered.max i j, stageMap F A₀ (IsFiltered.leftToMax i j) y +
      stageMap F A₀ (IsFiltered.rightToMax i j) w, ?_⟩
    rw [map_add, stageToLimitMap_comp_stageMap, stageToLimitMap_comp_stageMap]

/-- A finite family of elements of `R ⊗[R₀] A₀` comes from one stage. -/
private theorem exists_stage_tensor_finite_family {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    (c : Cocone F) (hc : ∀ x : c.pt, ∃ i y, (c.ι.app i).hom y = x)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] {σ : Type*} [Finite σ]
    (x : σ → c.pt ⊗[R₀] A₀) :
    ∃ (i : I) (y : σ → stageAlgebra F A₀ i), ∀ a, stageToLimitMap c A₀ i (y a) = x a := by
  classical
  let := Fintype.ofFinite σ
  choose i y hy using fun a ↦ exists_stage_tensor_element c hc A₀ (x a)
  let s := IsFiltered.cocone (Discrete.functor i)
  exact ⟨s.pt, fun a ↦ stageMap F A₀ (s.ι.app ⟨a⟩) (y a), fun a ↦
    (stageToLimitMap_comp_stageMap c A₀ (s.ι.app ⟨a⟩) (y a)).trans (hy a)⟩

/-- The transition maps of the stage algebras over a directed model `G : K ⥤ I` of the index
category. -/
private def stageDirectedMap {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] (F : I ⥤ CommAlgCat.{uR} R₀)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀]
    {K : Type*} [PartialOrder K] (G : K ⥤ I) (j k : K) (h : j ≤ k) :
    stageAlgebra F A₀ (G.obj j) →ₐ[R₀] stageAlgebra F A₀ (G.obj k) :=
  Algebra.TensorProduct.map (F.map (G.map (homOfLE h))).hom (AlgHom.id R₀ A₀)

private theorem stageDirectedMap_apply {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] (F : I ⥤ CommAlgCat.{uR} R₀)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀]
    {K : Type*} [PartialOrder K] (G : K ⥤ I) (j k : K) (h : j ≤ k) (y) :
    stageDirectedMap F A₀ G j k h y = stageMap F A₀ (G.map (homOfLE h)) y := rfl

/-- The maps between stage algebras are functorial. -/
private theorem stageMap_comp {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] (F : I ⥤ CommAlgCat.{uR} R₀)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] {a b d : I} (u : a ⟶ b) (v : b ⟶ d)
    (z : stageAlgebra F A₀ a) :
    stageMap F A₀ (u ≫ v) z = stageMap F A₀ v (stageMap F A₀ u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => simp [stageMap, Algebra.TensorProduct.map_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The stage algebras over a directed model form a directed system. -/
private theorem stageDirectedSystem {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] (F : I ⥤ CommAlgCat.{uR} R₀)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀]
    {K : Type*} [PartialOrder K] (G : K ⥤ I) :
    DirectedSystem (fun j : K ↦ stageAlgebra F A₀ (G.obj j))
      fun j k h ↦ ⇑(stageDirectedMap F A₀ G j k h) where
  map_self j y := by
    rw [stageDirectedMap_apply]
    have : G.map (homOfLE (le_refl j)) = 𝟙 _ := by
      rw [show homOfLE (le_refl j) = 𝟙 j from rfl, G.map_id]
    rw [this]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x a => simp [stageMap]
    | add y z hy hz => simp only [map_add, hy, hz]
  map_map {i j k} hij hjk y := by
    simp only [stageDirectedMap_apply]
    rw [← stageMap_comp, ← G.map_comp]
    rfl

/-- An element of a stage algebra that vanishes in the limit algebra vanishes at a later stage,
provided finite families of stage elements have this property. Uses flatness of `A₀`. -/
private theorem exists_stage_tensor_eq_zero {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] {F : I ⥤ CommAlgCat.{uR} R₀} (c : Cocone F)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀] {i : I}
    (hc : ∀ (k : ℕ) (x : Fin k → F.obj i), (∀ a, (c.ι.app i).hom (x a) = 0) →
      ∃ (j : I) (f : i ⟶ j), ∀ a, (F.map f).hom (x a) = 0)
    (y : stageAlgebra F A₀ i) (hy : stageToLimitMap c A₀ i y = 0) :
    ∃ (j : I) (f : i ⟶ j), stageMap F A₀ f y = 0 := by
  classical
  obtain ⟨T, rfl⟩ := TensorProduct.exists_finset y
  rw [← Finset.sum_coe_sort] at hy ⊢
  simp only [stageToLimitMap, map_sum, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq] at hy
  obtain ⟨k, a, z, hn, hm⟩ :=
    TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective
    R₀ (m := fun p : T ↦ (c.ι.app i).hom p.1.1) (n := fun p : T ↦ p.1.2)
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective) hy
  obtain ⟨j, f, hf⟩ := hc k (fun l ↦ ∑ p : T, a p l • p.1.1) (fun l ↦ by
    have h := hm l; simp only at h; rw [← h, map_sum]; simp only [map_smul])
  refine ⟨j, f, ?_⟩
  simp only [stageMap, map_sum, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  have hn' : ∀ p : T, p.1.2 = ∑ l, a p l • z l := hn
  simp_rw [hn', TensorProduct.tmul_sum, ← TensorProduct.smul_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  rw [← TensorProduct.sum_tmul]
  have := hf l
  simp only [map_sum, map_smul] at this
  rw [this, TensorProduct.zero_tmul]

/-- An element of a stage algebra that vanishes in the limit algebra vanishes at a later stage. -/
private theorem exists_stage_tensor_eq_zero_of_isColimit {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀] {i : I}
    (y : stageAlgebra F A₀ i) (hy : stageToLimitMap c A₀ i y = 0) :
    ∃ (j : I) (f : i ⟶ j), stageMap F A₀ f y = 0 := by
  refine exists_stage_tensor_eq_zero c A₀ (fun k x hx ↦ ?_) y hy
  obtain ⟨j, f, hf⟩ := exists_stage_finite_equalities hc x (fun _ ↦ 0)
    (fun a ↦ by rw [hx a, map_zero])
  exact ⟨j, f, fun a ↦ by rw [hf a, map_zero]⟩

set_option backward.isDefEq.respectTransparency false in
private def isColimit_stageUnderCocone_forget {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀] :
    IsColimit (((commAlgCatEquivUnder (CommRingCat.of (ULift.{uR} A₀))).inverse ⋙
      forget (CommAlgCat.{max uR uA} (ULift.{uR} A₀))).mapCocone (stageUnderCocone c A₀)) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := exists_stage_tensor_element c (exists_stage_element hc) A₀ x
    exact ⟨i, y, hy.symm⟩
  · intro i x y hxy
    change stageAlgebra F A₀ i at x y
    change stageToLimitMap c A₀ i x = stageToLimitMap c A₀ i y at hxy
    have hz : stageToLimitMap c A₀ i (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨j, f, hf⟩ := exists_stage_tensor_eq_zero_of_isColimit hc A₀ (x - y) hz
    refine ⟨j, f, ?_⟩
    change stageMap F A₀ f x = stageMap F A₀ f y
    exact sub_eq_zero.mp (by simpa only [map_sub] using hf)


/-- Along a final functor from a directed order, parallel maps into an image object become
equal further along. -/
private theorem final_exists_coeq_le {I : Type uI} [Category.{uJ} I] {K : Type*}
    [PartialOrder K] [IsDirectedOrder K] [Nonempty K] (G : K ⥤ I) [G.Final] {i : I} {k : K}
    (s s' : i ⟶ G.obj k) : ∃ (k' : K) (h : k ≤ k'),
      s ≫ G.map (homOfLE h) = s' ≫ G.map (homOfLE h) := by
  obtain ⟨k', t, ht⟩ := Functor.Final.exists_coeq G s s'
  exact ⟨k', leOfHom t, by rwa [show homOfLE (leOfHom t) = t from rfl]⟩

/-- Over a directed final model, every element of `R ⊗[R₀] A₀` comes from a stage. -/
private theorem exists_directed_stage_tensor_element {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀]
    {K : Type*} [PartialOrder K] [IsDirectedOrder K] [Nonempty K] (G : K ⥤ I) [G.Final]
    (x : c.pt ⊗[R₀] A₀) :
    ∃ (k : K) (y : stageAlgebra F A₀ (G.obj k)), stageToLimitMap c A₀ (G.obj k) y = x := by
  obtain ⟨i, y, rfl⟩ := exists_stage_tensor_element c (exists_stage_element hc) A₀ x
  obtain ⟨k, ⟨t⟩⟩ := ((Functor.final_iff_of_isFiltered G).1 inferInstance).1 i
  exact ⟨k, stageMap F A₀ t y, stageToLimitMap_comp_stageMap c A₀ t y⟩

/-- Over a directed final model, an element of a stage algebra vanishing in `R ⊗[R₀] A₀`
vanishes at a later stage. -/
private theorem exists_directed_stage_tensor_eq_zero {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    {K : Type*} [PartialOrder K] [IsDirectedOrder K] [Nonempty K] (G : K ⥤ I) [G.Final]
    {k : K} (y : stageAlgebra F A₀ (G.obj k)) (hy : stageToLimitMap c A₀ (G.obj k) y = 0) :
    ∃ (k' : K) (h : k ≤ k'), stageDirectedMap F A₀ G k k' h y = 0 := by
  obtain ⟨i, f, hf⟩ := exists_stage_tensor_eq_zero_of_isColimit hc A₀ y hy
  obtain ⟨k₁, ⟨t⟩⟩ := ((Functor.final_iff_of_isFiltered G).1 inferInstance).1 i
  obtain ⟨k₂, hk₁, hk₂⟩ := directed_of (· ≤ ·) k k₁
  obtain ⟨k', h', he⟩ := final_exists_coeq_le G (f ≫ t ≫ G.map (homOfLE hk₂))
    (G.map (homOfLE hk₁))
  refine ⟨k', hk₁.trans h', ?_⟩
  have hmap : G.map (homOfLE (hk₁.trans h')) = G.map (homOfLE hk₁) ≫ G.map (homOfLE h') := by
    rw [← G.map_comp]; rfl
  rw [stageDirectedMap_apply, hmap, ← he]
  simp only [Category.assoc, stageMap_comp F A₀ f, hf, map_zero]

/-- Over a directed final model, `R ⊗[R₀] A₀` is the directed colimit of the stage algebras:
the comparison map from `DirectLimit` is bijective. This is the hypothesis of 05N7. -/
private theorem stage_directLimit_lift_bijective {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    {K : Type*} [PartialOrder K] [IsDirectedOrder K] [Nonempty K] (G : K ⥤ I) [G.Final] :
    letI := stageDirectedSystem F A₀ G
    Function.Bijective (DirectLimit.Algebra.lift (fun k : K ↦ stageAlgebra F A₀ (G.obj k))
      (stageDirectedMap F A₀ G) (c.pt ⊗[R₀] A₀)
      (fun k ↦ Algebra.TensorProduct.map (c.ι.app (G.obj k)).hom (AlgHom.id R₀ A₀))
      (fun _ _ h y ↦ stageToLimitMap_comp_stageMap c A₀ (G.map (homOfLE h)) y)) := by
  let := stageDirectedSystem F A₀ G
  exact directLimit_algebra_lift_bijective _ _ _
    (fun x ↦ exists_directed_stage_tensor_element hc A₀ G x)
    (fun k y hy ↦ exists_directed_stage_tensor_eq_zero hc A₀ G y hy)

/-- A finitely presented module over `R ⊗[R₀] A₀` is the base change of a finitely presented
module over some stage algebra (Stacks 05N7, applied to a directed final model of `I`). -/
private theorem exists_directed_stage_finitePresentation_baseChange {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    {K : Type*} [PartialOrder K] [IsDirectedOrder K] [Nonempty K]
    (G : K ⥤ I) [G.Final]
    (M : Type*) [AddCommGroup M] [Module (c.pt ⊗[R₀] A₀) M]
    [Module.FinitePresentation (c.pt ⊗[R₀] A₀) M] :
    ∃ (k : K) (Mi : Type (max uR uA)) (_ : AddCommGroup Mi)
      (_ : Module (stageAlgebra F A₀ (G.obj k)) Mi),
      letI := (stageToLimitMap c A₀ (G.obj k)).toAlgebra
      Module.FinitePresentation (stageAlgebra F A₀ (G.obj k)) Mi ∧
        Nonempty ((c.pt ⊗[R₀] A₀) ⊗[stageAlgebra F A₀ (G.obj k)] Mi ≃ₗ[c.pt ⊗[R₀] A₀] M) := by
  let := stageDirectedSystem F A₀ G
  let : ∀ k : K, Algebra (stageAlgebra F A₀ (G.obj k)) (c.pt ⊗[R₀] A₀) := fun k ↦
    (stageToLimitMap c A₀ (G.obj k)).toAlgebra
  have htower : ∀ k : K, IsScalarTower R₀ (stageAlgebra F A₀ (G.obj k)) (c.pt ⊗[R₀] A₀) :=
    fun k ↦ IsScalarTower.of_algebraMap_eq fun r ↦
      ((Algebra.TensorProduct.map (c.ι.app (G.obj k)).hom (AlgHom.id R₀ A₀)).commutes r).symm
  have hbij := stage_directLimit_lift_bijective hc A₀ G
  obtain ⟨h1, -, -⟩ :=
    Module.exists_finitePresentation_and_baseChange_eq_of_lift_bijective.{_, _, _, _, 0}
    (stageDirectedMap F A₀ G)
    (fun _ _ h y ↦ stageToLimitMap_comp_stageMap c A₀ (G.map (homOfLE h)) y) hbij
  obtain ⟨k, Mk, _, _, hfp, ⟨e⟩⟩ := h1 M
  exact ⟨k, Mk, inferInstance, inferInstance, hfp, ⟨e⟩⟩


/-- The three items of 05N7 at the stages (applied to a directed final model of `I`):
finitely presented modules over `R ⊗[R₀] A₀` are base changes of finitely presented modules over
some stage algebra, and linear maps between base changes of `R₀`-modules, and equalities of
base-changed maps, descend to a stage algebra. -/
private theorem exists_stage_baseChange_descent.{uM', uN'} {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀] :
    (∀ (M : Type uM') [AddCommGroup M] [Module (c.pt ⊗[R₀] A₀) M]
        [Module.FinitePresentation (c.pt ⊗[R₀] A₀) M],
        ∃ (i : I) (Mi : Type (max uR uA)) (_ : AddCommGroup Mi)
          (_ : Module (stageAlgebra F A₀ i) Mi),
          letI := (stageToLimitMap c A₀ i).toAlgebra
          Module.FinitePresentation (stageAlgebra F A₀ i) Mi ∧
            Nonempty ((c.pt ⊗[R₀] A₀) ⊗[stageAlgebra F A₀ i] Mi ≃ₗ[c.pt ⊗[R₀] A₀] M)) ∧
    (∀ (M : Type uM') [AddCommGroup M] [Module R₀ M] [Module.FinitePresentation R₀ M]
        (N : Type uN') [AddCommGroup N] [Module R₀ N]
        (φ : (c.pt ⊗[R₀] A₀) ⊗[R₀] M →ₗ[c.pt ⊗[R₀] A₀] (c.pt ⊗[R₀] A₀) ⊗[R₀] N),
        ∃ (i : I) (φi : stageAlgebra F A₀ i ⊗[R₀] M →ₗ[stageAlgebra F A₀ i]
            stageAlgebra F A₀ i ⊗[R₀] N),
          ∀ x : stageAlgebra F A₀ i ⊗[R₀] M,
            φ (LinearMap.rTensor M
              (Algebra.TensorProduct.map (c.ι.app i).hom (AlgHom.id R₀ A₀)).toLinearMap x) =
              LinearMap.rTensor N
                (Algebra.TensorProduct.map (c.ι.app i).hom (AlgHom.id R₀ A₀)).toLinearMap
                (φi x)) ∧
    (∀ (M : Type uM') [AddCommGroup M] [Module R₀ M] [Module.Finite R₀ M]
        (N : Type uN') [AddCommGroup N] [Module R₀ N] (u u' : M →ₗ[R₀] N),
        u.baseChange (c.pt ⊗[R₀] A₀) = u'.baseChange (c.pt ⊗[R₀] A₀) →
          ∃ i : I, u.baseChange (stageAlgebra F A₀ i) = u'.baseChange (stageAlgebra F A₀ i)) := by
  obtain ⟨K, _, _, _, G, _⟩ := exists_directed_final I
  let := stageDirectedSystem F A₀ G
  let : ∀ k : K, Algebra (stageAlgebra F A₀ (G.obj k)) (c.pt ⊗[R₀] A₀) := fun k ↦
    (stageToLimitMap c A₀ (G.obj k)).toAlgebra
  have htower : ∀ k : K, IsScalarTower R₀ (stageAlgebra F A₀ (G.obj k)) (c.pt ⊗[R₀] A₀) :=
    fun k ↦ IsScalarTower.of_algebraMap_eq fun r ↦
      ((Algebra.TensorProduct.map (c.ι.app (G.obj k)).hom (AlgHom.id R₀ A₀)).commutes r).symm
  have hbij := stage_directLimit_lift_bijective hc A₀ G
  have h05N7 :=
    Module.exists_finitePresentation_and_baseChange_eq_of_lift_bijective.{_, _, _, uM', uN'}
    (stageDirectedMap F A₀ G)
    (fun _ _ h y ↦ stageToLimitMap_comp_stageMap c A₀ (G.map (homOfLE h)) y) hbij
  refine ⟨fun M _ _ _ ↦ ?_, fun M _ _ _ N _ _ φ ↦ ?_, fun M _ _ _ N _ _ u u' h ↦ ?_⟩
  · obtain ⟨k, Mk, _, _, hfp, he⟩ := h05N7.1 M
    exact ⟨G.obj k, Mk, inferInstance, inferInstance, hfp, he⟩
  · obtain ⟨k, φk, hk⟩ := h05N7.2.1 M N φ
    exact ⟨G.obj k, φk, hk⟩
  · obtain ⟨k, hk⟩ := h05N7.2.2 M N u u' h
    exact ⟨G.obj k, hk⟩

/-- Finitely presented modules descend to a stage of the original filtered category. -/
private theorem exists_stage_finitePresentation_baseChange {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    (M : Type*) [AddCommGroup M] [Module (c.pt ⊗[R₀] A₀) M]
    [Module.FinitePresentation (c.pt ⊗[R₀] A₀) M] :
    ∃ (i : I) (Mi : Type (max uR uA)) (_ : AddCommGroup Mi)
      (_ : Module (stageAlgebra F A₀ i) Mi),
      letI := (stageToLimitMap c A₀ i).toAlgebra
      Module.FinitePresentation (stageAlgebra F A₀ i) Mi ∧
        Nonempty ((c.pt ⊗[R₀] A₀) ⊗[stageAlgebra F A₀ i] Mi ≃ₗ[c.pt ⊗[R₀] A₀] M) := by
  exact (exists_stage_baseChange_descent.{_, _, _, _, _, 0} hc A₀).1 M

/-- The upper set of a directed order is directed. -/
private theorem isDirectedOrder_upperSet {K : Type*} [PartialOrder K] [IsDirectedOrder K]
    (k : K) : IsDirectedOrder {l : K // k ≤ l} := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨m, ha, hb⟩ := directed_of (· ≤ ·) a.1 b.1
  exact ⟨⟨m, a.2.trans ha⟩, ha, hb⟩

/-- Stacks 05N7 relative to the stage algebra `Aₖ`: over the stages above `k`, the algebra
`R ⊗[R₀] A₀` is the directed colimit of the `Aₗ`, as `Aₖ`-algebras. -/
private theorem stage_above_directLimit_lift_bijective {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    {K : Type*} [PartialOrder K] [IsDirectedOrder K] [Nonempty K] (G : K ⥤ I) [G.Final]
    (k : K) :
    letI := isDirectedOrder_upperSet k
    letI := fun l : {l : K // k ≤ l} ↦
      (stageDirectedMap F A₀ G k l.1 l.2).toRingHom.toAlgebra
    letI := (stageToLimitMap c A₀ (G.obj k)).toAlgebra
    letI := stageDirectedSystem F A₀ G
    ∃ (f : ∀ l l' : {l : K // k ≤ l}, l ≤ l' →
        stageAlgebra F A₀ (G.obj l.1) →ₐ[stageAlgebra F A₀ (G.obj k)]
          stageAlgebra F A₀ (G.obj l'.1))
      (_hf₀ : ∀ l l' h y, f l l' h y = stageDirectedMap F A₀ G l.1 l'.1 h y)
      (_ : DirectedSystem (fun l : {l : K // k ≤ l} ↦ stageAlgebra F A₀ (G.obj l.1))
        fun l l' h ↦ ⇑(f l l' h))
      (g : ∀ l : {l : K // k ≤ l}, stageAlgebra F A₀ (G.obj l.1) →ₐ[stageAlgebra F A₀ (G.obj k)]
          c.pt ⊗[R₀] A₀)
      (_hg₀ : ∀ l y, g l y = stageToLimitMap c A₀ (G.obj l.1) y)
      (hf : ∀ l l' h y, g l' (f l l' h y) = g l y),
      Function.Bijective (DirectLimit.Algebra.lift _ f _ g hf) := by
  let := isDirectedOrder_upperSet k
  let := stageDirectedSystem F A₀ G
  let := fun l : {l : K // k ≤ l} ↦
    (stageDirectedMap F A₀ G k l.1 l.2).toRingHom.toAlgebra
  let := (stageToLimitMap c A₀ (G.obj k)).toAlgebra
  have hmm := fun (a b d : K) (h₁ : a ≤ b) (h₂ : b ≤ d) (y : stageAlgebra F A₀ (G.obj a)) ↦
    DirectedSystem.map_map (f := fun j k h ↦ ⇑(stageDirectedMap F A₀ G j k h)) h₁ h₂ y
  let f : ∀ l l' : {l : K // k ≤ l}, l ≤ l' →
      stageAlgebra F A₀ (G.obj l.1) →ₐ[stageAlgebra F A₀ (G.obj k)]
        stageAlgebra F A₀ (G.obj l'.1) := fun l l' h ↦
    { stageDirectedMap F A₀ G l.1 l'.1 h with
      commutes' := fun y ↦ hmm _ _ _ l.2 h y }
  let g : ∀ l : {l : K // k ≤ l}, stageAlgebra F A₀ (G.obj l.1) →ₐ[stageAlgebra F A₀ (G.obj k)]
      c.pt ⊗[R₀] A₀ := fun l ↦
    { stageToLimitMap c A₀ (G.obj l.1) with
      commutes' := fun y ↦
        stageToLimitMap_comp_stageMap c A₀ (G.map (homOfLE l.2)) y }
  have hf : ∀ l l' h y, g l' (f l l' h y) = g l y := fun l l' h y ↦
    stageToLimitMap_comp_stageMap c A₀ (G.map (homOfLE h)) y
  have hds : DirectedSystem (fun l : {l : K // k ≤ l} ↦ stageAlgebra F A₀ (G.obj l.1))
      fun l l' h ↦ ⇑(f l l' h) :=
    { map_self := fun l y ↦ DirectedSystem.map_self
        (f := fun j k h ↦ ⇑(stageDirectedMap F A₀ G j k h)) y
      map_map := fun {_ _ _} h₁ h₂ y ↦ hmm _ _ _ h₁ h₂ y }
  refine ⟨f, fun _ _ _ _ ↦ rfl, hds, g, fun _ _ ↦ rfl, hf, ?_⟩
  refine directLimit_algebra_lift_bijective f g hf (fun r ↦ ?_) (fun l y hy ↦ ?_)
  · obtain ⟨m, y, rfl⟩ := exists_directed_stage_tensor_element hc A₀ G r
    obtain ⟨n, hkn, hmn⟩ := directed_of (· ≤ ·) k m
    exact ⟨⟨n, hkn⟩, stageDirectedMap F A₀ G m n hmn y,
      stageToLimitMap_comp_stageMap c A₀ (G.map (homOfLE hmn)) y⟩
  · obtain ⟨m, hlm, hm⟩ := exists_directed_stage_tensor_eq_zero hc A₀ G y hy
    exact ⟨⟨m, l.2.trans hlm⟩, hlm, hm⟩

/-- Stacks 05N7 applied to the stages above `k`, as algebras over the stage algebra `Aₖ`:
finitely presented modules, maps between base changes, and equalities of base-changed maps
over `R ⊗[R₀] A₀` all descend to some stage above `k`. -/
private theorem stage_above_finitePresentation_baseChange.{uM', uN'} {R₀ : Type uR}
    [CommRing R₀] {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    {K : Type*} [PartialOrder K] [IsDirectedOrder K] [Nonempty K] (G : K ⥤ I) [G.Final]
    (k : K) :
    letI := fun l : {l : K // k ≤ l} ↦
      (stageDirectedMap F A₀ G k l.1 l.2).toRingHom.toAlgebra
    letI := fun l : {l : K // k ≤ l} ↦ (stageToLimitMap c A₀ (G.obj l.1)).toAlgebra
    letI := (stageToLimitMap c A₀ (G.obj k)).toAlgebra
    ∃ (_ : ∀ l : {l : K // k ≤ l}, IsScalarTower (stageAlgebra F A₀ (G.obj k))
        (stageAlgebra F A₀ (G.obj l.1)) (c.pt ⊗[R₀] A₀)),
    (∀ (M : Type uM') [AddCommGroup M] [Module (stageAlgebra F A₀ (G.obj k)) M]
        [Module.FinitePresentation (stageAlgebra F A₀ (G.obj k)) M]
        (N : Type uN') [AddCommGroup N] [Module (stageAlgebra F A₀ (G.obj k)) N]
        (φ : (c.pt ⊗[R₀] A₀) ⊗[stageAlgebra F A₀ (G.obj k)] M →ₗ[c.pt ⊗[R₀] A₀]
          (c.pt ⊗[R₀] A₀) ⊗[stageAlgebra F A₀ (G.obj k)] N),
        ∃ (l : {l : K // k ≤ l})
          (φl : stageAlgebra F A₀ (G.obj l.1) ⊗[stageAlgebra F A₀ (G.obj k)] M →ₗ[
              stageAlgebra F A₀ (G.obj l.1)]
              stageAlgebra F A₀ (G.obj l.1) ⊗[stageAlgebra F A₀ (G.obj k)] N),
          ∀ x, φ (LinearMap.rTensor M (IsScalarTower.toAlgHom (stageAlgebra F A₀ (G.obj k))
              (stageAlgebra F A₀ (G.obj l.1)) (c.pt ⊗[R₀] A₀)).toLinearMap x) =
            LinearMap.rTensor N (IsScalarTower.toAlgHom (stageAlgebra F A₀ (G.obj k))
              (stageAlgebra F A₀ (G.obj l.1)) (c.pt ⊗[R₀] A₀)).toLinearMap (φl x)) ∧
    (∀ (M : Type uM') [AddCommGroup M] [Module (stageAlgebra F A₀ (G.obj k)) M]
        [Module.Finite (stageAlgebra F A₀ (G.obj k)) M]
        (N : Type uN') [AddCommGroup N] [Module (stageAlgebra F A₀ (G.obj k)) N]
        (u u' : M →ₗ[stageAlgebra F A₀ (G.obj k)] N),
        u.baseChange (c.pt ⊗[R₀] A₀) = u'.baseChange (c.pt ⊗[R₀] A₀) →
          ∃ l : {l : K // k ≤ l}, u.baseChange (stageAlgebra F A₀ (G.obj l.1)) =
            u'.baseChange (stageAlgebra F A₀ (G.obj l.1))) := by
  let := isDirectedOrder_upperSet k
  let := fun l : {l : K // k ≤ l} ↦
    (stageDirectedMap F A₀ G k l.1 l.2).toRingHom.toAlgebra
  let := fun l : {l : K // k ≤ l} ↦ (stageToLimitMap c A₀ (G.obj l.1)).toAlgebra
  let := (stageToLimitMap c A₀ (G.obj k)).toAlgebra
  have htower : ∀ l : {l : K // k ≤ l}, IsScalarTower (stageAlgebra F A₀ (G.obj k))
      (stageAlgebra F A₀ (G.obj l.1)) (c.pt ⊗[R₀] A₀) := fun l ↦
    IsScalarTower.of_algebraMap_eq fun y ↦
      (stageToLimitMap_comp_stageMap c A₀ (G.map (homOfLE l.2)) y).symm
  obtain ⟨f, hf₀, hds, g, hg₀, hf, hbij⟩ := stage_above_directLimit_lift_bijective hc A₀ G k
  have hg : ∀ l, g l = IsScalarTower.toAlgHom (stageAlgebra F A₀ (G.obj k))
      (stageAlgebra F A₀ (G.obj l.1)) (c.pt ⊗[R₀] A₀) := fun l ↦ AlgHom.ext (hg₀ l)
  have hf' : ∀ l l' (h : l ≤ l') y, algebraMap (stageAlgebra F A₀ (G.obj l'.1))
      (c.pt ⊗[R₀] A₀) (f l l' h y) = algebraMap (stageAlgebra F A₀ (G.obj l.1))
      (c.pt ⊗[R₀] A₀) y := fun l l' h y ↦ by
    simpa [hg] using hf l l' h y
  have hbij' : Function.Bijective (DirectLimit.Algebra.lift _ f (c.pt ⊗[R₀] A₀)
      (fun l ↦ IsScalarTower.toAlgHom (stageAlgebra F A₀ (G.obj k))
        (stageAlgebra F A₀ (G.obj l.1)) (c.pt ⊗[R₀] A₀)) hf') := by
    have hfun : (fun l : {l : K // k ≤ l} ↦ IsScalarTower.toAlgHom (stageAlgebra F A₀ (G.obj k))
        (stageAlgebra F A₀ (G.obj l.1)) (c.pt ⊗[R₀] A₀)) = g := funext fun l ↦ (hg l).symm
    subst hfun
    exact hbij
  have h05N7 :=
    Module.exists_finitePresentation_and_baseChange_eq_of_lift_bijective.{_, _, _, uM', uN'}
      f hf' hbij'
  exact ⟨htower, fun M _ _ _ N _ _ φ ↦ h05N7.2.1 M N φ, fun M _ _ _ N _ _ u u' h ↦
    h05N7.2.2 M N u u' h⟩

end PseudoCoherence

end
