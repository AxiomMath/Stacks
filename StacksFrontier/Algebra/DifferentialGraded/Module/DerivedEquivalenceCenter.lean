module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CentralActionTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceCompactGeneratorConverse
public import StacksFrontier.Algebra.DifferentialGraded.Module.EndomorphismCentral
public import StacksFrontier.Algebra.DifferentialGraded.Module.EndomorphismDGAQuasiIso
public import StacksFrontier.CategoryTheory.Center.Equivalence

/-!
# Derived equivalent algebras concentrated in degree zero have isomorphic centres

Let `R` be a commutative ring and let `S` and `T` be `R`-algebras, read as differential graded
algebras concentrated in degree zero. This file proves that if `D(S, d)` and `D(T, d)` are
equivalent by an additive, `R`-linear, shift-commuting equivalence, then the centres of `S` and
`T` are isomorphic as `R`-algebras. This is the differential graded form of [Stacks, Tag 09SD].

## The argument

A central element `s` of `S` acts on every differential graded `S`-module by right
multiplication, which gives an element `μ(s)` of the centre of the category `D(S, d)`
(`DifferentialGradedModule.derivedCentralSMul`). An arbitrary equivalence `D(S, d) ≌ D(T, d)`
carries no information about these elements; the point is to replace it by the equivalence of
the proof of [Stacks, Tag 09SA], which is assembled from derived tensor products and therefore
does.

Let `X` be an object of `D(T, d)` which is compact, weakly generating, without self-extensions
in nonzero degrees, and with endomorphism algebra `S` — for instance the image of `S` under the
given equivalence. Replace `X` by a property-(P) model `Q`, let `E = End(Q)` be its endomorphism
differential graded algebra, `E'` the degree-`≤ 0` truncation of `E`, and
$$D(S, d) \xleftarrow{\;\theta\;} D(E', d) \xrightarrow{\;\psi\;} D(E, d)
\xrightarrow{\;- \otimes_E^{\mathbf L} Q\;} D(T, d)$$
the equivalences of the proof of Tag 09SA. For a central element `w` of `T`, right
multiplication by `w` on `Q` is a central cocycle `r(w)` of `E` and of `E'`, and each of the
three functors carries the central action of `r(w)` (or of `θ(r(w))`) to the next one
(`DifferentialGraded.Bimodule.carries_derivedTensorFunctor`). So the composite equivalence
`Φ : D(S, d) ≌ D(T, d)` carries `μ(α(w))` to `μ(w)`, where `α(w) = θ(r(w))` is a central element
of `S` (`DifferentialGradedModule.exists_derivedEquivalence_carries_center`).

* `α` is injective: if `α(w) = 0` then `μ(w)` vanishes on the image of `Φ`, which is everything,
  in particular on `T`; and `μ(w)` at `T` is left multiplication by `w`.
* If `μ(s)` vanishes at an object `X'` of `D(S, d)` of the kind above for the pair `(S, T)`
  reversed, then `s = 0`: the construction for `X'` gives `Ψ : D(T, d) ≌ D(S, d)` with `Ψ(T) ≅ X'`
  and `β` with `Ψ` carrying `μ(β(s))` to `μ(s)`; at `T` this says `μ(β(s)) = 0` at `T`, so
  `β(s) = 0`, so `μ(s)` vanishes everywhere, so `s = 0`.
* `α` is surjective: given `s`, conjugating `μ(s)` by `Φ` and evaluating at `T` gives a central
  element `w` of `T`, and `μ(s - α(w))` vanishes at `Φ⁻¹(T)`, which is an object of the kind
  above; so `s = α(w)`.

## Main results

* `DifferentialGradedModule.exists_derivedEquivalence_carries_center`: the construction.
* `DifferentialGradedModule.nonempty_centerAlgEquiv_of_derivedEquivalence`: the centres of
  derived equivalent `R`-algebras are isomorphic as `R`-algebras.

## References

* [Stacks Project, Tag 09SD](https://stacks.math.columbia.edu/tag/09SD)
* [Stacks Project, Tag 09SA](https://stacks.math.columbia.edu/tag/09SA)
* J. Rickard, *Derived equivalences as derived functors*, Proposition 9.2.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGradedModule

open DifferentialGradedAlgebra DifferentialGraded.Bimodule CategoryTheory.ObjectProperty

variable {R : Type u} [CommRing R]

/-! ### Central elements of an algebra concentrated in degree zero -/

section Center

variable (S : Type u) [Ring S] [Algebra R S]

/-- The algebra `degreeZero R S` is concentrated in degree zero. -/
theorem grading_degreeZero_eq_bot : ∀ i : ℤ, i ≠ 0 → (degreeZero R S).grading i = ⊥ :=
  fun _ hi => degreeZeroGrading_eq_bot R S hi

/-- A central element of `S` is a central cocycle of degree zero of `degreeZero R S`. -/
theorem isCentralCocycle_degreeZero (s : Subalgebra.center R S) :
    IsCentralCocycle (E := degreeZero R S) (s : S) where
  comm b := (Subalgebra.mem_center_iff.1 s.2 b).symm
  mem := by
    rw [(degreeZero R S).grading_zero_eq_top (grading_degreeZero_eq_bot S)]
    exact Submodule.mem_top
  d_eq := rfl

/-- **The central action of `Z(S)` on `D(S, d)`.** A central element `s` of `S` acts on every
differential graded `S`-module by right multiplication, which defines an element of the centre
of the derived category. -/
def centerDerived : Subalgebra.center R S →+ CatCenter (derivedCategory' (degreeZero R S)) where
  toFun s := derivedCentralSMul (isCentralCocycle_degreeZero S s)
  map_zero' := derivedCentralSMul_zero _
  map_add' s t := derivedCentralSMul_add (isCentralCocycle_degreeZero S s)
    (isCentralCocycle_degreeZero S t) (isCentralCocycle_degreeZero S (s + t))

/-- The class in `D(S, d)` of the regular module. -/
abbrev regularObj : derivedCategory' (degreeZero R S) :=
  (toHomotopyCategory (degreeZero R S) ⋙ (quasiIsomorphisms' (degreeZero R S)).Q).obj
    (regularModule (degreeZero R S))

/-- On the regular module, the central action of `s` is left multiplication by `s`. -/
theorem centerDerived_app_regularObj (s : Subalgebra.center R S) :
    (centerDerived S s).app (regularObj S) =
      (regularEndAlgEquiv (degreeZero R S) (grading_degreeZero_eq_bot S) (s : S)).asHom := by
  change (derivedCentralSMul (isCentralCocycle_degreeZero S s)).app _ = _
  rw [derivedCentralSMul_app]
  change _ = (toHomotopyCategory _ ⋙ (quasiIsomorphisms' _).Q).map
    (regularMulLeft _ (degreeZeroCocycle _ (grading_degreeZero_eq_bot S) (s : S)))
  congr 1
  refine Hom.ext (LinearMap.ext fun x => ?_)
  rw [centralSMul_toFun_apply, regularMulLeft_toFun_apply]
  exact Subalgebra.mem_center_iff.1 s.2 x

/-- The central action is faithful on the regular module. -/
theorem eq_zero_of_centerDerived_app_regularObj (s : Subalgebra.center R S)
    (h : (centerDerived S s).app (regularObj S) = 0) : s = 0 := by
  rw [centerDerived_app_regularObj] at h
  have h' : ((s : S)) = 0 :=
    (regularEndAlgEquiv (degreeZero R S) (grading_degreeZero_eq_bot S)).injective
      ((End.ext h).trans (map_zero _).symm)
  exact Subtype.ext h'

end Center

/-! ### Central elements and isomorphisms -/

/-- The component of a central element at an object is its component at an isomorphic object,
conjugated by the isomorphism. -/
theorem _root_.CategoryTheory.CatCenter.app_eq_conj_of_iso {C : Type*} [Category C]
    (z : CatCenter C) {X Y : C} (e : X ≅ Y) : z.app X = e.hom ≫ z.app Y ≫ e.inv := by
  have h : e.hom ≫ z.app Y = z.app X ≫ e.hom := z.naturality e.hom
  rw [← Category.assoc, h, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The zero element of the centre vanishes at every object. -/
theorem _root_.CategoryTheory.CatCenter.zero_app' {C : Type*} [Category C] [Preadditive C]
    (X : C) : (0 : CatCenter C).app X = 0 :=
  rfl

/-- Two central elements which agree at an object agree at every isomorphic object. -/
theorem _root_.CategoryTheory.CatCenter.app_eq_app_of_iso {C : Type*} [Category C]
    (z z' : CatCenter C) {X Y : C} (e : X ≅ Y) (h : z.app Y = z'.app Y) : z.app X = z'.app X := by
  rw [z.app_eq_conj_of_iso e, z'.app_eq_conj_of_iso e, h]

/-- A central element of a preadditive category which vanishes at an object vanishes at every
isomorphic object. -/
theorem _root_.CategoryTheory.CatCenter.app_eq_zero_of_iso_of_app_eq_zero {C : Type*} [Category C]
    [Preadditive C] (z : CatCenter C) {X Y : C} (e : X ≅ Y) (h : z.app Y = 0) : z.app X = 0 := by
  rw [z.app_eq_conj_of_iso e, h, zero_comp, comp_zero]

/-! ### The tilting objects -/

/-- An object `X` of `D(T, d)` is a *tilting object with endomorphism algebra `S`* if it is
compact, weakly generates, has no self-extensions in nonzero degrees and has `S` as its
endomorphism `R`-algebra: the conditions of [Stacks, Tag 09S8] (2). -/
def IsTiltingObject (S : Type u) [Ring S] [Algebra R S] {T : Type u} [Ring T] [Algebra R T]
    (X : derivedCategory' (degreeZero R T)) : Prop :=
  IsCompactObject.{u} X ∧
    (∀ N : derivedCategory' (degreeZero R T), (∀ (i : ℤ) (f : X ⟶ N⟦i⟧), f = 0) → IsZero N) ∧
      (∀ i : ℤ, i ≠ 0 → ∀ f : X ⟶ X⟦i⟧, f = 0) ∧ Nonempty (S ≃ₐ[R] End X)

/-- The image of the regular module under an additive, `R`-linear, shift-commuting equivalence is
a tilting object: this is [Stacks, Tag 09S8], (1) ⇒ (2). -/
theorem isTiltingObject_functor_obj_regularObj {S T : Type u} [Ring S] [Algebra R S] [Ring T]
    [Algebra R T] (G : derivedCategory' (degreeZero R S) ≌ derivedCategory' (degreeZero R T))
    [G.functor.Additive] [G.functor.Linear R] [G.functor.CommShift ℤ] :
    IsTiltingObject S (G.functor.obj (regularObj S)) := by
  refine ⟨(isCompactObject_iff_isCompactObject_obj G.functor _).1
    (isCompactObject_q_regularModule (degreeZero R S)), ?_, ?_, ?_⟩
  · exact (isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero _).1
      (isWeakTriangulatedGenerator_obj_of_equivalence G _
        (isWeakTriangulatedGenerator_q_regularModule _))
  · intro i hi f
    exact (cohomologyEquivShiftHomFunctorObjRegularModule G i).symm.injective
      (@Subsingleton.elim _ ((degreeZero R S).subsingleton_cohomology
        (grading_degreeZero_eq_bot S) hi) _ _)
  · exact ⟨(regularEndAlgEquiv (degreeZero R S) (grading_degreeZero_eq_bot S)).trans
      (G.fullyFaithfulFunctor.algEquivEndOfFullyFaithful (R := R) _)⟩

/-! ### The construction -/

section Construction

variable {T : Type u} [Ring T] [Algebra R T]

/-- Right multiplication by a central element `w` of `T` on `Q`, as a morphism of degree zero of
the degree-`≤ 0` truncation of the differential graded category of `T`-modules. -/
private def truncatedCentralSMul (Q : DifferentialGradedModule.{u, u, u} (degreeZero R T))
    (w : Subalgebra.center R T) :
    (DGCategory.nonpositive (dgCategory.{u, u, u} (degreeZero R T))).Hom Q Q 0 :=
  ⟨centralSMulHomogeneous (isCentralCocycle_degreeZero T w) Q, fun h => absurd h (lt_irrefl 0),
    fun _ => homogeneousMapDifferential_centralSMulHomogeneous _ Q⟩

/-- The element of the truncated endomorphism algebra `E'` given by right multiplication by `w`. -/
private def truncatedElement (Q : DifferentialGradedModule.{u, u, u} (degreeZero R T))
    (w : Subalgebra.center R T) :
    (DGCategory.homRepresentation
      (DGCategory.nonpositive (dgCategory.{u, u, u} (degreeZero R T))) Q).algebra.A :=
  (((DGCategory.homRepresentation
      (DGCategory.nonpositive (dgCategory.{u, u, u} (degreeZero R T))) Q).algebraHom 0).symm
    (truncatedCentralSMul Q w) : _)

private theorem isCentralCocycle_truncatedElement
    (Q : DifferentialGradedModule.{u, u, u} (degreeZero R T)) (w : Subalgebra.center R T) :
    IsCentralCocycle (truncatedElement Q w) :=
  DGCategory.HomRepresentation.isCentralCocycle_algebraHom_symm _ _
    (Subtype.ext (homogeneousMapDifferential_centralSMulHomogeneous _ Q))
    (fun n g => Subtype.ext (homogeneousMapComp_centralSMulHomogeneous _ Q n g.1))

/-- The element of `E = End(Q)` given by right multiplication by `w`. -/
private def endElement (Q : DifferentialGradedModule.{u, u, u} (degreeZero R T))
    (w : Subalgebra.center R T) : (endomorphismDGA (degreeZero R T) Q).A :=
  ((endomorphismAlgebraHom (degreeZero R T) Q 0).symm
    (centralSMulHomogeneous (isCentralCocycle_degreeZero T w) Q) : _)

private theorem isCentralCocycle_endElement
    (Q : DifferentialGradedModule.{u, u, u} (degreeZero R T)) (w : Subalgebra.center R T) :
    IsCentralCocycle (endElement Q w) :=
  DGCategory.HomRepresentation.isCentralCocycle_algebraHom_symm _ _
    (homogeneousMapDifferential_centralSMulHomogeneous _ Q)
    (fun n g => homogeneousMapComp_centralSMulHomogeneous _ Q n g)

/-- Right multiplication by `w` in the truncated endomorphism algebra, as an `R`-algebra
homomorphism out of the centre of `T`. -/
private def truncatedAlgHom (Q : DifferentialGradedModule.{u, u, u} (degreeZero R T)) :
    Subalgebra.center R T →ₐ[R]
      (DGCategory.homRepresentation
        (DGCategory.nonpositive (dgCategory.{u, u, u} (degreeZero R T))) Q).algebra.A where
  toFun := truncatedElement Q
  map_one' := by
    have h : truncatedCentralSMul Q 1 =
        (DGCategory.nonpositive (dgCategory.{u, u, u} (degreeZero R T))).id Q :=
      Subtype.ext (centralSMulHomogeneous_one _ Q)
    unfold truncatedElement
    rw [h]
    exact DGCategory.HomRepresentation.algebraHom_symm_id _
  map_mul' w w' := by
    have h : truncatedCentralSMul Q (w * w') =
        (DGCategory.nonpositive (dgCategory.{u, u, u} (degreeZero R T))).comp (add_zero 0)
          (truncatedCentralSMul Q w) (truncatedCentralSMul Q w') :=
      Subtype.ext (centralSMulHomogeneous_mul (isCentralCocycle_degreeZero T w)
        (isCentralCocycle_degreeZero T w') _ Q)
    unfold truncatedElement
    rw [h]
    exact DGCategory.HomRepresentation.algebraHom_symm_comp _ _ _
  map_zero' := by
    have h : truncatedCentralSMul Q 0 = 0 := Subtype.ext (centralSMulHomogeneous_zero _ Q)
    unfold truncatedElement
    rw [h, map_zero, Submodule.coe_zero]
  map_add' w w' := by
    have h : truncatedCentralSMul Q (w + w') =
        truncatedCentralSMul Q w + truncatedCentralSMul Q w' :=
      Subtype.ext (centralSMulHomogeneous_add (isCentralCocycle_degreeZero T w)
        (isCentralCocycle_degreeZero T w') _ Q)
    unfold truncatedElement
    rw [h, map_add, Submodule.coe_add]
  commutes' r := by
    have h : truncatedCentralSMul Q (algebraMap R _ r) =
        r • (DGCategory.nonpositive (dgCategory.{u, u, u} (degreeZero R T))).id Q :=
      Subtype.ext (centralSMulHomogeneous_algebraMap r _ Q)
    unfold truncatedElement
    rw [h, map_smul, Submodule.coe_smul, DGCategory.HomRepresentation.algebraHom_symm_id,
      Algebra.algebraMap_eq_smul_one]

/-- The image under `θ` of a central cocycle of `E'` is central, when `θ` is a quasi-isomorphism
onto an algebra concentrated in degree zero: every element of the target is then the image of a
cocycle. -/
private theorem mem_center_of_isCentralCocycle {S : Type u} [Ring S] [Algebra R S]
    {E' : DifferentialGradedAlgebra.{u, u} R} (θ : E'.Hom (degreeZero R S))
    (hθ : Function.Bijective (θ.cohomologyMap 0)) {c : E'.A} (hc : IsCentralCocycle c) :
    θ.toAlgebraHom c ∈ Subalgebra.center R S := by
  rw [Subalgebra.mem_center_iff]
  intro s
  obtain ⟨y, hy⟩ := hθ.2 (((degreeZero R S).cohomologyZeroEquiv
    (grading_degreeZero_eq_bot S)).symm s)
  induction y using Quotient.ind with | _ a => ?_
  have ha : θ.toAlgebraHom (a.1 : E'.A) = s := by
    have h := congrArg ((degreeZero R S).cohomologyZeroEquiv (grading_degreeZero_eq_bot S)) hy
    rw [Equiv.apply_symm_apply, DifferentialGradedAlgebra.Hom.cohomologyMap_mk] at h
    exact h
  rw [← ha, ← map_mul, ← map_mul, hc.comm]

/-- **The construction.** Let `X` be a tilting object of `D(T, d)` with endomorphism algebra `S`.
Then there are an additive, `R`-linear, shift-commuting equivalence `Φ : D(S, d) ≌ D(T, d)`
sending `S` to `X` and a homomorphism of `R`-algebras `α : Z(T) → Z(S)` such that `Φ` carries the
central action of `α(w)` to the central action of `w`, for every `w`; moreover `Φ⁻¹(T)` is a
tilting object of `D(S, d)` with endomorphism algebra `T`.

The equivalence is the one of the proof of [Stacks, Tag 09SA], assembled from the two
quasi-isomorphisms `(S, d) ← (E', d) → (E, d)` out of the truncated endomorphism algebra of a
property-(P) model `Q` of `X`, and the bimodule `Q` over `E = End(Q)`. Right multiplication by `w`
on `Q` is a central cocycle `r(w)` of `E'`, and `α(w)` is its image in `S`. -/
theorem exists_derivedEquivalence_carries_center (S : Type u) [Ring S] [Algebra R S]
    (X : derivedCategory' (degreeZero R T)) (hX : IsTiltingObject S X) :
    ∃ (Φ : derivedCategory' (degreeZero R S) ≌ derivedCategory' (degreeZero R T))
      (α : Subalgebra.center R T →ₐ[R] Subalgebra.center R S),
      Nonempty (Φ.functor.obj (regularObj S) ≅ X) ∧
        IsTiltingObject T (Φ.inverse.obj (regularObj T)) ∧
          ∀ w, CatCenter.Carries Φ.functor (centerDerived S (α w)) (centerDerived T w) := by
  obtain ⟨hcompact, hgen, hvan, ⟨ea⟩⟩ := hX
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := exists_propertyPFiltration_model (degreeZero R T) X
  have hwQ := isWeakTriangulatedGenerator_singleton_of_iso eQ.symm
    ((isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero X).2 hgen)
  have hvanish : ∀ k : ℤ, k ≠ 0 →
      ∀ f : (toHomotopyCategory (degreeZero R T) ⋙ (quasiIsomorphisms' (degreeZero R T)).Q).obj Q
        ⟶ (toHomotopyCategory (degreeZero R T) ⋙
          (quasiIsomorphisms' (degreeZero R T)).Q).obj (Q.shift k), f = 0 := fun k hk f =>
    (Iso.homCongr eQ (shiftCompare Q k ≪≫
      (CategoryTheory.shiftFunctor (derivedCategory' (degreeZero R T)) k).mapIso eQ)).injective
      ((hvan k hk _).trans (hvan k hk _).symm)
  obtain ⟨θ, hθ⟩ := exists_hom_nonpositiveEndomorphismDGA_to_concentrated (degreeZero R S)
    (degreeZero R T) (grading_degreeZero_eq_bot S) Q hQ hvanish
    (ea.trans (Iso.endAlgEquiv (R := R) eQ.symm))
  obtain ⟨ψ, hψ, hψf⟩ := exists_hom_nonpositiveEndomorphismDGA_bijective_cohomologyMap_algebraHom
    (degreeZero R T) Q hQ (fun k hk => hvanish k hk.ne')
  have : IsCompactObject.{u} ((toHomotopyCategory (degreeZero R T) ⋙
      (quasiIsomorphisms' (degreeZero R T)).Q).obj
        (endomorphism (degreeZero R T) Q).rightModule) := isCompactObject_of_iso eQ hcompact
  have h2 := (isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero _).1 hwQ
  have h3 := bijective_cohomologyEndomorphismComparison_endomorphism (degreeZero R T) Q hQ
  let Eth := derivedExtensionEquivalence θ hθ
  let Eps := derivedExtensionEquivalence ψ hψ
  let EQ := derivedTensorEquivalence (endomorphism (degreeZero R T) Q) h2 h3
  -- The homomorphism `α`.
  have hcent : ∀ w, (θ.toAlgebraHom.comp (truncatedAlgHom Q)) w ∈ Subalgebra.center R S :=
    fun w => mem_center_of_isCentralCocycle θ (hθ 0) (isCentralCocycle_truncatedElement Q w)
  let α := (θ.toAlgebraHom.comp (truncatedAlgHom Q)).codRestrict (Subalgebra.center R S) hcent
  refine ⟨Eth.symm.trans (Eps.trans EQ), α, ?_, ?_, fun w => ?_⟩
  · -- The value on the regular module.
    have key : ∀ {Y Z : DifferentialGradedAlgebra.{u, u} R} (N : DifferentialGraded.Bimodule Y Z),
        (derivedTensorFunctor N).obj ((toHomotopyCategory Y ⋙ (quasiIsomorphisms' Y).Q).obj
          (regularModule Y)) ≅
        (toHomotopyCategory Z ⋙ (quasiIsomorphisms' Z).Q).obj N.rightModule :=
      fun N => derivedTensorIsoOfLeftOrthogonal N (regularModule _)
        (leftOrthogonal_acyclic_toHomotopyCategory_regularModule _) (tensorRegularIso N).1
    let rthinv : Eth.inverse.obj (regularObj S) ≅ (toHomotopyCategory _ ⋙
        (quasiIsomorphisms' _).Q).obj (regularModule _) :=
      Eth.inverse.mapIso (key (DifferentialGraded.Bimodule.regular θ)).symm ≪≫
        (Eth.unitIso.app _).symm
    exact ⟨(Eps.functor ⋙ EQ.functor).mapIso rthinv ≪≫
      EQ.functor.mapIso (key (DifferentialGraded.Bimodule.regular ψ)) ≪≫
        key (endomorphism (degreeZero R T) Q) ≪≫ eQ⟩
  · -- The inverse image of the regular module is a tilting object.
    let Ψ := EQ.symm.trans (Eps.symm.trans Eth)
    have : EQ.inverse.CommShift ℤ := EQ.commShiftInverse ℤ
    have : Ψ.functor.Additive := by
      change (EQ.inverse ⋙ Eps.inverse ⋙ Eth.functor).Additive
      infer_instance
    have : Ψ.functor.Linear R := by
      change (EQ.inverse ⋙ Eps.inverse ⋙ Eth.functor).Linear R
      infer_instance
    have : Ψ.functor.CommShift ℤ := by
      change (EQ.inverse ⋙ Eps.inverse ⋙ Eth.functor).CommShift ℤ
      infer_instance
    exact isTiltingObject_functor_obj_regularObj Ψ
  · -- The functor carries the central actions.
    have hr := isCentralCocycle_endElement Q w
    have hr' := isCentralCocycle_truncatedElement Q w
    have hθw : IsCentralCocycle (θ.toAlgebraHom (truncatedElement Q w)) :=
      isCentralCocycle_degreeZero S (α w)
    have hψw : ψ.toAlgebraHom (truncatedElement Q w) = endElement Q w := by
      have h := hψf 0 (((DGCategory.homRepresentation (DGCategory.nonpositive
        (dgCategory.{u, u, u} (degreeZero R T))) Q).algebraHom 0).symm (truncatedCentralSMul Q w))
      rw [LinearEquiv.apply_symm_apply] at h
      exact congrArg Subtype.val ((LinearEquiv.eq_symm_apply _).2 h)
    have hEQ : CatCenter.Carries EQ.functor (derivedCentralSMul hr)
        (centerDerived T w) := by
      refine carries_derivedTensorFunctor (endomorphism (degreeZero R T) Q) hr
        (isCentralCocycle_degreeZero T w) fun y => ?_
      rw [endomorphism_leftMultiplication]
      change (endomorphismAlgebraHom (degreeZero R T) Q 0 ((endomorphismAlgebraHom
        (degreeZero R T) Q 0).symm (centralSMulHomogeneous _ Q))).1 y = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    have hEps : CatCenter.Carries Eps.functor (derivedCentralSMul hr') (derivedCentralSMul hr) := by
      refine carries_derivedTensorFunctor (DifferentialGraded.Bimodule.regular ψ) hr' hr
        fun y => (regular_leftMultiplication_zero ⟨_, hr'.mem⟩ (fun b => ?_) y).trans ?_
      · rw [hψw]
        exact hr.comm b
      · change MulOpposite.op (ψ.toAlgebraHom (truncatedElement Q w)) • y = _
        rw [hψw]
    have hEth : CatCenter.Carries Eth.functor (derivedCentralSMul hr')
        (derivedCentralSMul hθw) := by
      exact carries_derivedTensorFunctor (DifferentialGraded.Bimodule.regular θ) hr' hθw
        fun y => regular_leftMultiplication_zero ⟨_, hr'.mem⟩ (fun b => hθw.comm b) y
    exact (CatCenter.Carries.inverse Eth hEth).comp (hEps.comp hEQ)

end Construction

/-! ### The centres -/

/-- **Derived equivalent algebras have isomorphic centres.** Let `S` and `T` be algebras over a
commutative ring `R`, read as differential graded algebras concentrated in degree zero, and let
`G : D(S, d) ≌ D(T, d)` be an additive, `R`-linear, shift-commuting equivalence. Then the centres
of `S` and `T` are isomorphic as `R`-algebras. -/
theorem nonempty_centerAlgEquiv_of_derivedEquivalence (S T : Type u) [Ring S] [Algebra R S]
    [Ring T] [Algebra R T]
    (G : derivedCategory' (degreeZero R S) ≌ derivedCategory' (degreeZero R T))
    [G.functor.Additive] [G.functor.Linear R] [G.functor.CommShift ℤ] :
    Nonempty (Subalgebra.center R S ≃ₐ[R] Subalgebra.center R T) := by
  obtain ⟨Φ, α, -, hT, hα⟩ :=
    exists_derivedEquivalence_carries_center S _ (isTiltingObject_functor_obj_regularObj G)
  obtain ⟨Φ₂, β, ⟨e₂⟩, -, hβ⟩ := exists_derivedEquivalence_carries_center T _ hT
  -- A central element of `S` acting by zero on the tilting object `Φ⁻¹(T)` is zero.
  have hL : ∀ s : Subalgebra.center R S,
      (centerDerived S s).app (Φ.inverse.obj (regularObj T)) = 0 → s = 0 := by
    intro s hs
    have hβs : β s = 0 := by
      apply eq_zero_of_centerDerived_app_regularObj T
      apply Φ₂.functor.map_injective
      rw [hβ s, Functor.map_zero]
      exact (centerDerived S s).app_eq_zero_of_iso_of_app_eq_zero e₂ hs
    apply eq_zero_of_centerDerived_app_regularObj S
    refine (centerDerived S s).app_eq_zero_of_iso_of_app_eq_zero
      (Φ₂.counitIso.app (regularObj S)).symm ?_
    change (centerDerived S s).app (Φ₂.functor.obj (Φ₂.inverse.obj (regularObj S))) = 0
    rw [← hβ s, hβs, map_zero, CatCenter.zero_app', Functor.map_zero]
  have hinj : Function.Injective α := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply eq_zero_of_centerDerived_app_regularObj T
    refine (centerDerived T w).app_eq_zero_of_iso_of_app_eq_zero
      (Φ.counitIso.app (regularObj T)).symm ?_
    change (centerDerived T w).app (Φ.functor.obj (Φ.inverse.obj (regularObj T))) = 0
    rw [← hα w, hw, map_zero, CatCenter.zero_app', Functor.map_zero]
  have hsurj : Function.Surjective α := by
    intro s
    let ξ := CatCenter.transport Φ (centerDerived S s)
    let rT := regularEndAlgEquiv (degreeZero R T) (grading_degreeZero_eq_bot T)
    have hw : rT.symm (End.of (ξ.app (regularObj T))) ∈ Subalgebra.center R T := by
      rw [Subalgebra.mem_center_iff]
      intro b
      apply rT.injective
      rw [map_mul, map_mul, rT.apply_symm_apply]
      exact End.ext (ξ.naturality (rT b).asHom).symm
    let w : Subalgebra.center R T := ⟨_, hw⟩
    refine ⟨w, ?_⟩
    have hwT : (centerDerived T w).app (regularObj T) = ξ.app (regularObj T) := by
      rw [centerDerived_app_regularObj]
      exact congrArg End.asHom (rT.apply_symm_apply _)
    have h1 := CatCenter.app_eq_app_of_iso (centerDerived T w) ξ
      (Φ.counitIso.app (regularObj T)) hwT
    have h2 : (centerDerived S (α w)).app (Φ.inverse.obj (regularObj T)) =
        (centerDerived S s).app (Φ.inverse.obj (regularObj T)) := by
      apply Φ.functor.map_injective
      rw [hα w]
      exact h1.trans (CatCenter.transport_app_functor Φ _ _)
    have h3 := hL (s - α w) (by rw [map_sub, CatCenter.app_sub, h2, sub_self])
    exact (sub_eq_zero.1 h3).symm
  exact ⟨(AlgEquiv.ofBijective α ⟨hinj, hsurj⟩).symm⟩

end DifferentialGradedModule

end
