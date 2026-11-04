module

public import StacksFrontier.Deformation.TangentSpace.LinearFunctor

/-!
# Linear lifts and tensor descriptions of product-preserving functors

A set-valued functor on finite-dimensional vector spaces which takes the zero module to a
one-element set and turns products into products has a canonical linear lift, and that lift
is tensoring with its value on a rank-one module.

## Main definitions

* `Deformation.linearFunctorLiftOfProductConditions`: the canonical linear lift of a
  set-valued functor on finitely generated modules satisfying the zero and product
  conditions.
* `Deformation.rankOneTensorComparison`: the canonical map
  `L(E) ⊗[K] V → L(V)` attached to a rank-one object `E` with a chosen coordinate.
* `Deformation.rankOneTensorEquiv`: that map is a linear equivalence.

## Main results

* `Deformation.rankOneTensorComparison_tmul`: the value on a pure tensor.
* `Deformation.rankOneTensorEquiv_naturality`: the equivalences commute with every linear
  map.

## Implementation notes

`Deformation.linearFunctorLiftOfProductConditions` generalizes
`Deformation.tangentSpaceModuleStructure` (Stacks 06IA), which states the same construction
only for functors presented as `Deformation.tangentSpaceSetFunctor S R P hP F` and only when
the universe of the modules equals the universe of the base ring. Tag 06IH needs the
construction for an arbitrary functor `FGModuleCat.{z} k ⥤ Type u₁`, because the square-zero
extensions it is applied to live in the carrier universe of the Artinian algebras rather than
in the universe of the residue field. The existing declaration does not suffice and is a
specialization of this one: its proof uses its subcategory data only to form the functor.

The tensor description is stated for an arbitrary rank-one object `E` together with a linear
coordinate `K ≃ₗ[K] E`, so that the same declarations serve both the plain rank-one module `K`
and the universe-lifted `ULift K` used by the Artinian dual numbers. It refines the
categorical isomorphism of Stacks 06I8 by giving the map on pure tensors explicitly; Stacks
06I8 itself is in `StacksFrontier/Deformation/TangentSpace/LinearFunctor.lean`.

## References

* [Stacks Project, Tag 06I8](https://stacks.math.columbia.edu/tag/06I8)
* [Stacks Project, Tag 06IA](https://stacks.math.columbia.edu/tag/06IA)
-/

@[expose] public section

namespace Deformation

/-! ### The canonical linear lift -/

section Lift
open CategoryTheory CategoryTheory.Limits
universe uR uM vM

/-- A set-valued functor on finitely generated `R`-modules whose value at the zero module is a
one-element set and which turns the two product projections into a bijection onto the product
of sets has a canonical additive, `R`-linear lift. -/
noncomputable def linearFunctorLiftOfProductConditions
    (R : Type uR) [CommRing R] (L : FGModuleCat.{vM} R ⥤ Type uM)
    (hzero : Nonempty (L.obj (FGModuleCat.of R PUnit)))
    (hsubsingleton : Subsingleton (L.obj (FGModuleCat.of R PUnit)))
    (hprod : ∀ M N : FGModuleCat.{vM} R, Function.Bijective
      (fun x : L.obj (FGModuleCat.of R (M × N)) ↦
        (L.map (FGModuleCat.ofHom (LinearMap.fst R M N)) x,
          L.map (FGModuleCat.ofHom (LinearMap.snd R M N)) x))) :
    LinearFunctorLift R L :=
  let prodIsLimit := fun M N : FGModuleCat.{vM} R ↦ Limits.BinaryFan.isLimitMk
    (fun s ↦ FGModuleCat.ofHom (LinearMap.prod s.fst.hom.hom s.snd.hom.hom))
    (fun _ ↦ by ext; rfl) (fun _ ↦ by ext; rfl)
    (fun _ f hf hg ↦ by
      ext x
      · exact congrArg (fun q ↦ q.hom.hom x) hf
      · exact congrArg (fun q ↦ q.hom.hom x) hg)
  let : Unique (L.obj (FGModuleCat.of R PUnit)) :=
    { default := Classical.choice hzero, uniq := fun _ ↦ hsubsingleton.elim _ _ }
  let : ∀ X : FGModuleCat.{vM} R, Nonempty (X ⟶ FGModuleCat.of R PUnit) :=
    fun _ ↦ ⟨FGModuleCat.ofHom 0⟩
  let : ∀ X : FGModuleCat.{vM} R, Subsingleton (X ⟶ FGModuleCat.of R PUnit) :=
    fun _ ↦ ⟨fun _ _ ↦ by ext⟩
  let : Limits.HasTerminal (FGModuleCat.{vM} R) :=
    Limits.hasTerminal_of_unique (FGModuleCat.of R PUnit)
  let : ∀ M N : FGModuleCat.{vM} R, Limits.HasLimit (Limits.pair M N) :=
    fun M N ↦ ⟨⟨Limits.BinaryFan.mk
      (FGModuleCat.ofHom (LinearMap.fst R M N) : FGModuleCat.of R (M × N) ⟶ M)
      (FGModuleCat.ofHom (LinearMap.snd R M N)), prodIsLimit M N⟩⟩
  let : Limits.HasBinaryProducts (FGModuleCat.{vM} R) :=
    Limits.hasBinaryProducts_of_hasLimit_pair _
  let : Limits.HasFiniteProducts (FGModuleCat.{vM} R) :=
    CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal
  let : ∀ M N : FGModuleCat.{vM} R, Limits.PreservesLimit (Limits.pair M N) L :=
    fun M N ↦ Limits.preservesLimit_of_preserves_limit_cone (prodIsLimit M N)
      ((Limits.isLimitMapConeBinaryFanEquiv L
          (FGModuleCat.ofHom (LinearMap.fst R M N) : FGModuleCat.of R (M × N) ⟶ M)
          (FGModuleCat.ofHom (LinearMap.snd R M N))).symm
        (let e := Equiv.ofBijective _ (hprod M N)
         Limits.BinaryFan.isLimitMk
          (fun s ↦ ↾fun x ↦ e.symm (s.fst x, s.snd x))
          (fun s ↦ by ext x; exact congrArg Prod.fst (e.apply_symm_apply (s.fst x, s.snd x)))
          (fun s ↦ by ext x; exact congrArg Prod.snd (e.apply_symm_apply (s.fst x, s.snd x)))
          (fun s f hf hg ↦ by
            ext x
            apply e.injective
            change e (f x) = e (e.symm (s.fst x, s.snd x))
            rw [e.apply_symm_apply]
            dsimp [e]
            apply Prod.ext
            · simpa using congrArg (fun q ↦ (ConcreteCategory.hom q) x) hf
            · simpa using congrArg (fun q ↦ (ConcreteCategory.hom q) x) hg)))
  let : Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) L :=
    { preservesLimit := by
        intro K
        exact Limits.preservesLimit_of_iso_diagram L (Limits.diagramIsoPair K).symm }
  let : Limits.PreservesLimitsOfShape (Discrete PEmpty) L :=
    { preservesLimit := by
        intro K
        let c : Limits.Cone K := Limits.Cone.mk (FGModuleCat.of R PUnit)
          { app := fun j ↦ nomatch j.as
            naturality := fun X _ _ ↦ PEmpty.elim X.as }
        let hc : Limits.IsLimit c :=
          { lift := fun _ ↦ FGModuleCat.ofHom 0
            fac := fun _ j ↦ nomatch j.as
            uniq := fun _ _ _ ↦ Subsingleton.elim _ _ }
        apply Limits.preservesLimit_of_preserves_limit_cone hc
        let : Unique (L.mapCone c).pt :=
          { default := (default : L.obj (FGModuleCat.of R PUnit))
            uniq := fun a ↦ hsubsingleton.elim a _ }
        exact (Limits.Types.isLimit_iff_bijective_sectionOfCone _).mpr
          ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
            fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩ |>.some }
  let : Limits.PreservesFiniteProducts L :=
    Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal L
  fgModuleCatLinearFunctorLift R L

end Lift

/-! ### Tensoring with the value on a rank-one module -/

section Tensor
open CategoryTheory
universe w u₁ z

variable (K : Type w) [Field K]

/-- Addition of morphisms of finitely generated modules acts pointwise on vectors. -/
theorem fgModuleCat_add_apply {V W : FGModuleCat.{z} K} (f g : V ⟶ W) (x : V) :
    (f + g).hom x = f.hom x + g.hom x := rfl

/-- The tautological coordinate on the rank-one module `K`. -/
noncomputable def rankOneCoord : K ≃ₗ[K] (FGModuleCat.of K K : FGModuleCat.{w} K) :=
  LinearEquiv.refl K K

/-- The coordinate on the universe-lifted rank-one module `ULift K`. -/
noncomputable def uliftRankOneCoord :
    K ≃ₗ[K] (FGModuleCat.of K (ULift.{z} K) : FGModuleCat.{max z w} K) :=
  ULift.moduleEquiv.symm

variable {E : FGModuleCat.{z} K} (eE : K ≃ₗ[K] E)

/-- The map out of a rank-one object determined by a vector, read through the chosen
coordinate on that object. -/
def rankOneSpan (V : FGModuleCat.{z} K) : V →ₗ[K] (E ⟶ V) where
  toFun v := FGModuleCat.ofHom
    ((LinearMap.toSpanSingleton K V v).comp eE.symm.toLinearMap)
  map_add' x y := by
    apply FGModuleCat.hom_ext
    ext r
    exact smul_add (eE.symm r) x y
  map_smul' r x := by
    apply FGModuleCat.hom_ext
    ext a
    exact smul_comm (eE.symm a) r x

/-- The map `rankOneSpan K eE V v` sends `r` to `eE.symm r • v`. -/
@[simp]
theorem rankOneSpan_apply (V : FGModuleCat.{z} K) (v : V) (r : E) :
    (rankOneSpan K eE V v).hom r = eE.symm r • v :=
  rfl

variable (L : FGModuleCat.{z} K ⥤ ModuleCat.{u₁} K) [L.Additive] [L.Linear K]
variable (T : Type u₁) [AddCommGroup T] [Module K T] (e : (L.obj E : Type u₁) ≃ₗ[K] T)

/-- The canonical map from `T ⊗[K] V` to `L(V)`, where `T` is identified with the value of
`L` on the rank-one object. -/
def rankOneTensorComparison (V : FGModuleCat.{z} K) :
    TensorProduct K T V →ₗ[K] (L.obj V : Type u₁) :=
  TensorProduct.lift <| LinearMap.mk₂ K
    (fun x v ↦ (L.map (rankOneSpan K eE V v)).hom (e.symm x))
    (fun x y v ↦ by
      rw [e.symm.map_add]
      exact map_add _ _ _)
    (fun r x v ↦ by
      change (L.map (rankOneSpan K eE V v)).hom (e.symm (r • x)) = _
      rw [e.symm.map_smul]
      exact map_smul _ _ _)
    (fun x v₁ v₂ ↦ by
      rw [map_add, L.map_add]
      rfl)
    (fun r x v ↦ by
      change (L.map (rankOneSpan K eE V (r • v))).hom (e.symm x) = _
      rw [map_smul, L.map_smul]
      rfl)

/-- The comparison map sends `x ⊗ₜ v` to the image of `e.symm x` under `L` applied to
`rankOneSpan K eE V v`. -/
@[simp]
theorem rankOneTensorComparison_tmul (V : FGModuleCat.{z} K) (x : T) (v : V) :
    rankOneTensorComparison K eE L T e V (x ⊗ₜ[K] v) =
      (L.map (rankOneSpan K eE V v)).hom (e.symm x) :=
  rfl

/-- The basis-coordinate inverse to `Deformation.rankOneTensorComparison`. -/
noncomputable def rankOneTensorComparisonInv (V : FGModuleCat.{z} K) :
    (L.obj V : Type u₁) →ₗ[K] TensorProduct K T V :=
  let b := Module.finBasis K V
  { toFun := fun y ↦ ∑ i,
      e ((L.map (FGModuleCat.ofHom
        (eE.symm.symm.toLinearMap.comp (b.coord i)))).hom y) ⊗ₜ[K] b i
    map_add' := fun x y ↦ by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
    map_smul' := fun r x ↦ by simp [TensorProduct.smul_tmul, Finset.smul_sum] }

/-- The comparison map followed by its basis-coordinate inverse is the identity. -/
theorem rankOneTensorComparisonInv_comp (V : FGModuleCat.{z} K) :
    rankOneTensorComparison K eE L T e V ∘ₗ rankOneTensorComparisonInv K eE L T e V =
      LinearMap.id := by
  let b := Module.finBasis K V
  refine LinearMap.ext fun y ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  dsimp [rankOneTensorComparisonInv]
  rw [map_sum]
  simp only [rankOneTensorComparison_tmul]
  show (∑ i, (L.map (rankOneSpan K eE V (b i))).hom
    (e.symm (e ((L.map (FGModuleCat.ofHom
      (eE.symm.symm.toLinearMap.comp (b.coord i)))).hom y)))) = y
  simp only [e.symm_apply_apply]
  have heq (i) : (L.map (rankOneSpan K eE V (b i))).hom
      ((L.map (FGModuleCat.ofHom
        (eE.symm.symm.toLinearMap.comp (b.coord i)))).hom y) =
      (L.map ((FGModuleCat.ofHom
          (eE.symm.symm.toLinearMap.comp (b.coord i)) : V ⟶ E) ≫
        rankOneSpan K eE V (b i))).hom y := by
    rw [← ModuleCat.comp_apply, ← L.map_comp]
  simp_rw [heq]
  have h : (∑ i, (FGModuleCat.ofHom
      (eE.symm.symm.toLinearMap.comp (b.coord i)) : V ⟶ E) ≫
      rankOneSpan K eE V (b i)) = 𝟙 V := by
    apply FGModuleCat.hom_ext
    ext v
    have eval_sum (s : Finset (Fin (Module.finrank K V))) :
        ModuleCat.Hom.hom (∑ i ∈ s,
          (FGModuleCat.ofHom
            (eE.symm.symm.toLinearMap.comp (b.coord i)) : V ⟶ E) ≫
            rankOneSpan K eE V (b i)).hom v = ∑ i ∈ s, b.repr v i • b i := by
      classical
      induction s using Finset.induction with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi, fgModuleCat_add_apply, ih]
          have hterm : ((FGModuleCat.ofHom
              (eE.symm.symm.toLinearMap.comp (b.coord i)) : V ⟶ E) ≫
              rankOneSpan K eE V (b i)).hom v = b.repr v i • b i := by
            show eE.symm (eE (b.coord i v)) • b i = b.repr v i • b i
            rw [eE.symm_apply_apply]
            rfl
          rw [hterm]
    rw [eval_sum Finset.univ, b.sum_repr]
    rfl
  calc
    _ = (L.map (∑ i, (FGModuleCat.ofHom
        (eE.symm.symm.toLinearMap.comp (b.coord i)) : V ⟶ E) ≫
        rankOneSpan K eE V (b i))).hom y := by
          rw [L.map_sum]
          simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
    _ = y := by rw [h, L.map_id]; rfl

/-- The basis-coordinate inverse followed by the comparison map is the identity. -/
theorem rankOneTensorComparison_comp (V : FGModuleCat.{z} K) :
    rankOneTensorComparisonInv K eE L T e V ∘ₗ rankOneTensorComparison K eE L T e V =
      LinearMap.id := by
  let b := Module.finBasis K V
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
      show (∑ i, e ((L.map (FGModuleCat.ofHom
        (eE.symm.symm.toLinearMap.comp (b.coord i)))).hom
          ((L.map (rankOneSpan K eE V v)).hom (e.symm x))) ⊗ₜ[K] b i) = x ⊗ₜ[K] v
      have h (i) : rankOneSpan K eE V v ≫ FGModuleCat.ofHom
          (eE.symm.symm.toLinearMap.comp (b.coord i)) =
          (b.repr v i) • 𝟙 E := by
        refine FGModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
        show eE (b.coord i (eE.symm r • v)) = b.repr v i • r
        rw [Module.Basis.coord_apply, b.repr.map_smul, Finsupp.smul_apply,
          smul_eq_mul, mul_comm, ← smul_eq_mul, eE.map_smul, eE.apply_symm_apply]
      have heq (i) : e ((L.map (FGModuleCat.ofHom
          (eE.symm.symm.toLinearMap.comp (b.coord i)))).hom
          ((L.map (rankOneSpan K eE V v)).hom (e.symm x))) = b.repr v i • x := by
        rw [← ModuleCat.comp_apply, ← L.map_comp, h, L.map_smul, L.map_id]
        simp
      simp_rw [heq, TensorProduct.smul_tmul]
      rw [← TensorProduct.tmul_sum, b.sum_repr]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- A linear functor on finite-dimensional vector spaces is tensoring with its value at a
rank-one module. -/
noncomputable def rankOneTensorEquiv (V : FGModuleCat.{z} K) :
    TensorProduct K T V ≃ₗ[K] (L.obj V : Type u₁) :=
  LinearEquiv.ofBijective (rankOneTensorComparison K eE L T e V) (by
    constructor
    · intro x y hxy
      have h := congrArg (rankOneTensorComparisonInv K eE L T e V) hxy
      simpa only [← LinearMap.comp_apply, rankOneTensorComparison_comp,
        LinearMap.id_apply] using h
    · intro y
      refine ⟨rankOneTensorComparisonInv K eE L T e V y, ?_⟩
      have h := congrArg (fun f : (L.obj V : Type u₁) →ₗ[K] (L.obj V : Type u₁) => f y)
        (rankOneTensorComparisonInv_comp K eE L T e V)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h)

/-- The rank-one tensor equivalence sends `x ⊗ₜ v` to the image of `e.symm x` under `L` applied
to `rankOneSpan K eE V v`. -/
@[simp]
theorem rankOneTensorEquiv_tmul (V : FGModuleCat.{z} K) (x : T) (v : V) :
    rankOneTensorEquiv K eE L T e V (x ⊗ₜ[K] v) =
      (L.map (rankOneSpan K eE V v)).hom (e.symm x) :=
  rfl

/-- The rank-one tensor equivalences commute with every linear map between
finite-dimensional vector spaces. -/
theorem rankOneTensorEquiv_naturality (V W : FGModuleCat.{z} K) (f : V ⟶ W)
    (z : TensorProduct K T V) :
    (L.map f).hom (rankOneTensorEquiv K eE L T e V z) =
      rankOneTensorEquiv K eE L T e W
        (TensorProduct.map (LinearMap.id : T →ₗ[K] T) f.hom.hom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t v =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, rankOneTensorEquiv_tmul,
        rankOneTensorEquiv_tmul]
      have h : rankOneSpan K eE W (f.hom.hom v) = rankOneSpan K eE V v ≫ f :=
        FGModuleCat.hom_ext <| LinearMap.ext fun r ↦ (f.hom.hom.map_smul (eE.symm r) v).symm
      rw [h, Functor.map_comp]
      rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Tensor

end Deformation
