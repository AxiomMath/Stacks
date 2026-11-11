module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyFlatExtension
public import StacksFrontier.Homology.RelativelyPerfect.BaseChange
public import StacksFrontier.Homology.Tor.BaseChangeCohomologyDevissage
public import StacksFrontier.Homology.Tor.ChangeOfRingsSystem
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# Cohomology of an iterated derived base change along a flat square

Consider a commutative diagram of commutative rings `A' ← R' → B'` over `A ← R → B` with `R'` flat
over `R`, `A'` flat over `A ⊗_R R'` and `B'` flat over `R' ⊗_R B`. For `M ∈ D(A)` this file
constructs the isomorphism of `A' ⊗_{R'} B'`-modules of [stacks 0DJD]

`H^i((M ⊗ᴸ_A A') ⊗ᴸ_{R'} B') ≅ (A' ⊗_{R'} B') ⊗_{A ⊗_R B} H^i(M ⊗ᴸ_R B)`,

where `M ⊗ᴸ_A A'` is read over `R'` and `M` is read over `R`, and the tensor-product module
structures are those of `RingTheory.TorIndependence.baseChangeCohomology`.

The proof follows the source. Write `B₀ = R' ⊗_R B`. First the case `B' = B₀`: reading the
derived base change over `R` instead of `R'` is the comparison of Stacks 065Z for the square
`R → R'`, `R → B`, which is invertible because `R → R'` is flat (Stacks 0661); and the flat map
`A → A'` passes through the cohomology of a derived base change over `R`
(`RingTheory.TorIndependence.localizedBaseChangeCohomologyIso`). This identifies
`H^i((M ⊗ᴸ_A A') ⊗ᴸ_{R'} B₀)` with `(A' ⊗_{R'} B₀) ⊗_{A ⊗_R B} H^i(M ⊗ᴸ_R B)`. The general case
follows by the flat base change `B₀ → B'` on cohomology
(`RingTheory.TorIndependence.flatCompDerivedHomologyIso`).

At each of the two steps the comparison is the transpose of an explicit semilinear map, and it
is invertible because it factors a bijection through a surjection.

## Main results

* `RingTheory.TorIndependence.baseChangeCohomologyIsoOfFlat`: the isomorphism of [stacks 0DJD].

## References

* [The Stacks Project, Tag 0DJD](https://stacks.math.columbia.edu/tag/0DJD)
* [The Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

open CategoryTheory CategoryTheory.Limits Functor
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

namespace FlatSquare

variable {R R' A B A' B' : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
  [CommRing A'] [CommRing B']
  [Algebra R R'] [Algebra R A] [Algebra R B]
  [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [Algebra R' A'] [IsScalarTower R R' A']
  [Algebra B B'] [Algebra R B'] [IsScalarTower R B B'] [Algebra R' B'] [IsScalarTower R R' B']

variable (R R' B B') in
/-- The comparison `R' ⊗_R B → B'` of the right-hand column of the square. -/
def rightTensorHom : R' ⊗[R] B →ₐ[R'] B' :=
  Algebra.TensorProduct.lift (Algebra.ofId R' B') (IsScalarTower.toAlgHom R B B')
    fun _ _ ↦ Commute.all _ _

variable (R R' A A') in
/-- The comparison `A ⊗_R R' → A'` of the left-hand column of the square. -/
def leftTensorHom : A ⊗[R] R' →ₐ[R] A' :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A A') (IsScalarTower.toAlgHom R R' A')
    fun _ _ ↦ Commute.all _ _

variable (R R' A B A' B') in
/-- The ring map `A ⊗_R B → A' ⊗_{R'} B'` induced by the square. -/
abbrev tensorHom : A ⊗[R] B →+* A' ⊗[R'] B' :=
  TorChangeOfRings.tensorProductMap R R' A B A' B' (IsScalarTower.toAlgHom R A A')
    (IsScalarTower.toAlgHom R B B')

variable (R R' A B A') in
/-- The ring map `A ⊗_R B → A' ⊗_{R'} (R' ⊗_R B)`. -/
abbrev midHom : A ⊗[R] B →+* A' ⊗[R'] (R' ⊗[R] B) :=
  TorChangeOfRings.tensorProductMap R R' A B A' (R' ⊗[R] B) (IsScalarTower.toAlgHom R A A')
    Algebra.TensorProduct.includeRight

variable (R R' B A' B') in
/-- The ring map `A' ⊗_{R'} (R' ⊗_R B) → A' ⊗_{R'} B'`. -/
abbrev topHom : A' ⊗[R'] (R' ⊗[R] B) →+* A' ⊗[R'] B' :=
  (Algebra.TensorProduct.map (AlgHom.id R' A') (rightTensorHom R R' B B')).toRingHom

theorem rightTensorHom_comp_algebraMap :
    (rightTensorHom R R' B B').toRingHom.comp (algebraMap R' (R' ⊗[R] B)) = algebraMap R' B' := by
  ext r
  simp [rightTensorHom]

theorem topHom_comp_midHom :
    (topHom R R' B A' B').comp (midHom R R' A B A') = tensorHom R R' A B A' B' := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [RingHom.comp_apply] at hx hy ⊢
    rw [_root_.map_add, _root_.map_add, _root_.map_add, hx, hy]
  | tmul a b =>
    simp [TorChangeOfRings.tensorProductMap, rightTensorHom]

theorem flat_algebraMap_left (hR' : (algebraMap R R').Flat)
    (hA' : (leftTensorHom R R' A A').toRingHom.Flat) : (algebraMap A A').Flat := by
  have hR : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hR'
  have h : (algebraMap A (A ⊗[R] R')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  convert h.comp hA' using 1
  ext a
  simp [leftTensorHom]

/-! ### Extension of scalars on elements -/

/-- Extension of scalars carries `1 ⊗ r • m` to `f r • (1 ⊗ m)`. -/
theorem extendScalars_one_tmul_smul {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    {M : ModuleCat.{u} S} (r : S) (m : M) :
    (show (ModuleCat.extendScalars.{u, u, u} f).obj M from (1 : T) ⊗ₜ[S, f] (r • m)) =
      f r • (show (ModuleCat.extendScalars.{u, u, u} f).obj M from (1 : T) ⊗ₜ[S, f] m) := by
  let := f.toAlgebra
  change (1 : T) ⊗ₜ[S] (r • m) = (f r * 1) ⊗ₜ[S] m
  rw [mul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one]

/-- A map out of an extension of scalars on a pure tensor `t ⊗ m`. -/
theorem extendScalars_hom_tmul {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    {M : ModuleCat.{u} S} {P : ModuleCat.{u} T} (φ : (ModuleCat.extendScalars.{u, u, u} f).obj M ⟶
        P)
    (t : T) (m : M) :
    φ.hom (t ⊗ₜ[S, f] m) = t • φ.hom ((1 : T) ⊗ₜ[S, f] m) :=
  ((congrArg (fun s : T => φ.hom (s ⊗ₜ[S, f] m)) (mul_one t).symm).trans
    (congrArg φ.hom (ModuleCat.ExtendScalars.smul_tmul f t (1 : T) m).symm)).trans
    (φ.hom.map_smul t _)

/-- Induction over the elements of an extension of scalars. -/
theorem extendScalars_induction {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    {M : ModuleCat.{u} S} {P : (ModuleCat.extendScalars.{u, u, u} f).obj M → Prop}
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (htmul : ∀ (t : T) (m : M), P (t ⊗ₜ[S,f] m))
    (x : (ModuleCat.extendScalars.{u, u, u} f).obj M) :
    P x :=
  TensorProduct.induction_on (motive := P) x h0 htmul hadd


/-- Restricting scalars along `g` and acting by `x` on `1 ⊗ m` gives `g x ⊗ m`. -/
theorem restrict_extendScalars_smul_one_tmul {S T U : Type u} [CommRing S] [CommRing T]
    [CommRing U] (f : S →+* T) (g : U →+* T) {M : ModuleCat.{u} S} (x : U) (m : M) :
    x • (show (ModuleCat.restrictScalars.{u} g).obj ((ModuleCat.extendScalars.{u, u, u} f).obj M)
        from (1 : T) ⊗ₜ[S, f] m) =
      (show (ModuleCat.restrictScalars.{u} g).obj ((ModuleCat.extendScalars.{u, u, u} f).obj M)
        from g x ⊗ₜ[S, f] m) :=
  (ModuleCat.ExtendScalars.smul_tmul f (g x) (1 : T) m).trans
    (congrArg (fun s : T => s ⊗ₜ[S, f] m) (mul_one (g x)))

/-- A function is bijective as soon as its composite with a surjection is. -/
theorem bijective_of_bijective_comp {α β γ : Type*} {f : β → γ} {g : α → β}
    (hg : Function.Surjective g) (h : Function.Bijective (f ∘ g)) : Function.Bijective f :=
  ⟨fun x y hxy => by
    obtain ⟨a, rfl⟩ := hg x
    obtain ⟨b, rfl⟩ := hg y
    exact congrArg g (h.1 hxy), fun z => let ⟨a, ha⟩ := h.2 z; ⟨g a, ha⟩⟩

/-! ### The right-hand column: flat base change along `R' ⊗_R B → B'` -/

section Right

variable [HasDerivedCategory.{u} (ModuleCat.{u} R')] [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} B')] [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))]

omit [Algebra R A'] [IsScalarTower R R' A'] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
  [HasDerivedCategory.{u} (ModuleCat.{u} A')] [HasDerivedCategory.{u} (ModuleCat.{u} B')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))] in
theorem topHom_includeLeft (a' : A') :
    topHom R R' B A' B' (Algebra.TensorProduct.includeLeft (R := R') (S := R') a') =
      Algebra.TensorProduct.includeLeft (R := R') (S := R') a' := by
  simp [topHom]

omit [Algebra R A'] [IsScalarTower R R' A'] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
  [HasDerivedCategory.{u} (ModuleCat.{u} A')] [HasDerivedCategory.{u} (ModuleCat.{u} B')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))] in
theorem topHom_includeRight (β : R' ⊗[R] B) :
    topHom R R' B A' B' (Algebra.TensorProduct.includeRight β) =
      Algebra.TensorProduct.includeRight (rightTensorHom R R' B B' β) := by
  simp [topHom]

/-- Flat base change along `R' ⊗_R B → B'` on the cohomology of a derived base change from
`R'`. -/
def rightFlatHomologyIso (hB' : (rightTensorHom R R' B B').toRingHom.Flat) (i : ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R' B')).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} B') i ≅
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} (R' ⊗[R] B)) i ⋙
          ModuleCat.extendScalars.{u, u, u} (rightTensorHom R R' B B').toRingHom :=
  eqToIso (congrArg (fun φ : R' →+* B' => (totalDerivedExtensionScalars.{u, u, u} φ).functor ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} B') i)
      (rightTensorHom_comp_algebraMap (R := R) (R' := R') (B := B) (B' := B')).symm) ≪≫
    flatCompDerivedHomologyIso.{u, u} (algebraMap R' (R' ⊗[R] B))
      (rightTensorHom R R' B B').toRingHom hB' i

variable (hB' : (rightTensorHom R R' B B').toRingHom.Flat) (N : DerivedCategory (ModuleCat.{u} A'))
  (i : ℤ)

/-- `m ↦ (flat base change)⁻¹ (1 ⊗ m)`, from the cohomology over `R' ⊗_R B` to the cohomology
over `B'`, as a map of `R' ⊗_R B`-modules. -/
def rightUnit :
    baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i ⟶
      (ModuleCat.restrictScalars.{u} (rightTensorHom R R' B B').toRingHom).obj
        (baseChangeCohomologyOverBase (R := R') (R' := B') N i) :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (rightTensorHom R R' B B').toRingHom).unit.app _ ≫
    (ModuleCat.restrictScalars.{u} (rightTensorHom R R' B B').toRingHom).map
      ((rightFlatHomologyIso hB' i).inv.app
        ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.obj N))

/-- `rightUnit` as an additive map between the two tensor-product modules. -/
def rightUnitAdd :
    (baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i : Type u) →+
      ((ModuleCat.restrictScalars.{u} (topHom R R' B A' B')).obj
        (baseChangeCohomology (R := R') (R' := B') N i) : Type u) where
  toFun m := (rightUnit hB' N i).hom m
  map_zero' := (rightUnit hB' N i).hom.map_zero
  map_add' := (rightUnit hB' N i).hom.map_add

/-- `rightUnit` as a map of `A' ⊗_{R'} (R' ⊗_R B)`-modules. -/
def rightComparison :
    baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i ⟶
      (ModuleCat.restrictScalars.{u} (topHom R R' B A' B')).obj
        (baseChangeCohomology (R := R') (R' := B') N i) :=
  ModuleCat.ofHom
    (X := (baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i : Type u))
    (Y := ((ModuleCat.restrictScalars.{u} (topHom R R' B A' B')).obj
        (baseChangeCohomology (R := R') (R' := B') N i) : Type u))
    (tensorLinearMapOfIncludes (R := R') (A := A') (S := R' ⊗[R] B)
    (rightUnitAdd hB' N i)
    (fun a' m =>
      (congrArg (rightUnitAdd hB' N i)
        (baseChangeCohomology_includeLeft_smul (R := R') (R' := R' ⊗[R] B) N i a' m)).trans
      ((DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp ((rightFlatHomologyIso hB' i).inv.naturality
          ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.map (a' • 𝟙 N))))
          ((1 : B') ⊗ₜ[R' ⊗[R] B, (rightTensorHom R R' B B').toRingHom]
            (show baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i from m))).trans
      ((baseChangeCohomology_includeLeft_smul (R := R') (R' := B') N i a'
          (rightUnitAdd hB' N i m)).symm.trans
        (congrArg (fun x => x • (show baseChangeCohomology (R := R') (R' := B') N i from
            rightUnitAdd hB' N i m)) (topHom_includeLeft a').symm))))
    (fun β m =>
      (congrArg (rightUnitAdd hB' N i)
        (baseChangeCohomology_includeRight_smul (R := R') (R' := R' ⊗[R] B) N i β m)).trans
      (((rightUnit hB' N i).hom.map_smul β
          (show baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i from m)).trans
      ((baseChangeCohomology_includeRight_smul (R := R') (R' := B') N i
          (rightTensorHom R R' B B' β) (rightUnitAdd hB' N i m)).symm.trans
        (congrArg (fun x => x • (show baseChangeCohomology (R := R') (R' := B') N i from
            rightUnitAdd hB' N i m)) (topHom_includeRight β).symm)))))

omit [Algebra R A'] [IsScalarTower R R' A'] in
theorem rightComparison_apply (m : baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i) :
    (rightComparison hB' N i).hom m =
      ((rightFlatHomologyIso hB' i).inv.app
        ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.obj N)).hom
        ((1 : B') ⊗ₜ[R' ⊗[R] B, (rightTensorHom R R' B B').toRingHom] m) :=
  rfl


/-- `m ↦ 1 ⊗ m`, from the cohomology over `R' ⊗_R B` to its extension of scalars to
`A' ⊗_{R'} B'`, as a map of `R' ⊗_R B`-modules. -/
def rightGen :
    baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i ⟶
      (ModuleCat.restrictScalars.{u} (rightTensorHom R R' B B').toRingHom).obj
        ((ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).obj
          ((ModuleCat.extendScalars.{u, u, u} (topHom R R' B A' B')).obj
            (baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i))) :=
  ModuleCat.ofHom
    (X := (baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i : Type u))
    (Y := ((ModuleCat.restrictScalars.{u} (rightTensorHom R R' B B').toRingHom).obj
        ((ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).obj
          ((ModuleCat.extendScalars.{u, u, u} (topHom R R' B A' B')).obj
            (baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i))) : Type u))
    { toFun := fun m => (1 : A' ⊗[R'] B') ⊗ₜ[A' ⊗[R'] (R' ⊗[R] B), topHom R R' B A' B']
        (show baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i from m)
      map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
      map_smul' := fun β m =>
        (congrArg (fun z => (show (ModuleCat.extendScalars.{u, u, u}
            (topHom R R' B A' B')).obj (baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i) from
            (1 : A' ⊗[R'] B') ⊗ₜ[A' ⊗[R'] (R' ⊗[R] B), topHom R R' B A' B'] z))
          (baseChangeCohomology_includeRight_smul (R := R') (R' := R' ⊗[R] B) N i β m).symm).trans
        ((extendScalars_one_tmul_smul (topHom R R' B A' B')
            (Algebra.TensorProduct.includeRight β) _).trans
          (congrArg (fun z => z • (show (ModuleCat.extendScalars.{u, u, u}
            (topHom R R' B A' B')).obj (baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i) from
            (1 : A' ⊗[R'] B') ⊗ₜ[A' ⊗[R'] (R' ⊗[R] B), topHom R R' B A' B'] m))
            (topHom_includeRight β))) }

/-- The `B'`-linear map `B' ⊗_{R' ⊗_R B} H ⟶ (A' ⊗_{R'} B') ⊗_{A' ⊗_{R'} (R' ⊗_R B)} H`,
`b' ⊗ m ↦ (1 ⊗ b') ⊗ m`. -/
def rightGenTranspose :
    (ModuleCat.extendScalars.{u, u, u} (rightTensorHom R R' B B').toRingHom).obj
        (baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i) ⟶
      (ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).obj
        ((ModuleCat.extendScalars.{u, u, u} (topHom R R' B A' B')).obj
          (baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i)) :=
  ModuleCat.extendScalarsTranspose _ (rightGen N i)

/-- The comparison `(A' ⊗_{R'} B') ⊗_{A' ⊗_{R'} (R' ⊗_R B)} H ⟶ K`. -/
def rightTranspose :
    (ModuleCat.extendScalars.{u, u, u} (topHom R R' B A' B')).obj
        (baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i) ⟶
      baseChangeCohomology (R := R') (R' := B') N i :=
  ModuleCat.extendScalarsTranspose _ (rightComparison hB' N i)


omit [Algebra R A'] [IsScalarTower R R' A'] in
theorem rightTranspose_one_tmul
    (m : baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i) :
    (rightTranspose hB' N i).hom
        ((1 : A' ⊗[R'] B') ⊗ₜ[A' ⊗[R'] (R' ⊗[R] B), topHom R R' B A' B'] m) =
      (rightComparison hB' N i).hom m :=
  ModuleCat.extendScalarsTranspose_one_tmul _ _ m

omit [Algebra R A'] [IsScalarTower R R' A'] [HasDerivedCategory.{u} (ModuleCat.{u} B')] in
theorem rightGenTranspose_one_tmul
    (m : baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i) :
    (rightGenTranspose (R := R) (R' := R') (B := B) (B' := B') N i).hom
        ((1 : B') ⊗ₜ[R' ⊗[R] B, (rightTensorHom R R' B B').toRingHom] m) =
      (rightGen (R := R) (R' := R') (B := B) (B' := B') N i).hom m :=
  ModuleCat.extendScalarsTranspose_one_tmul _ _ m

/-- The identity of `H^i(N|_{R'} ⊗ᴸ_{R'} B')`, read as the `A' ⊗_{R'} B'`-module
`baseChangeCohomology` restricted to `B'`. -/
def rightRestrictHom :
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R' B')).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} B') i).obj
        ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.obj N) ⟶
      (ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).obj
        (baseChangeCohomology (R := R') (R' := B') N i) :=
  ModuleCat.ofHom
    (X := (baseChangeCohomologyOverBase (R := R') (R' := B') N i : Type u))
    (Y := ((ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).obj
        (baseChangeCohomology (R := R') (R' := B') N i) : Type u))
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun r m =>
        (baseChangeCohomology_includeRight_smul (R := R') (R' := B') N i r m).symm }

omit [Algebra R A'] [IsScalarTower R R' A'] in
theorem rightTranspose_rightGen
    (m : baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i) :
    ((ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).map
        (rightTranspose hB' N i)).hom ((rightGen (R := R) (R' := R') (B := B) (B' := B') N
            i).hom m) =
      (rightRestrictHom (R' := R') (B' := B') N i).hom
        (((rightFlatHomologyIso hB' i).inv.app
          ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.obj N)).hom
          ((1 : B') ⊗ₜ[R' ⊗[R] B, (rightTensorHom R R' B B').toRingHom] m)) :=
  (rightTranspose_one_tmul hB' N i m).trans (rightComparison_apply hB' N i m)

omit [Algebra R A'] [IsScalarTower R R' A'] in
theorem rightTranspose_rightGenTranspose
    (x : (ModuleCat.extendScalars.{u, u, u} (rightTensorHom R R' B B').toRingHom).obj
      (baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i)) :
    ((ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).map
        (rightTranspose hB' N i)).hom
        ((rightGenTranspose (R := R) (R' := R') (B := B) (B' := B') N i).hom x) =
      (rightRestrictHom (R' := R') (B' := B') N i).hom
        (((rightFlatHomologyIso hB' i).inv.app
          ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.obj
              N)).hom x) := by
  induction x using extendScalars_induction with
  | h0 => simp only [_root_.map_zero]
  | hadd x y hx hy => simp only [_root_.map_add, hx, hy]
  | htmul t m =>
    refine (congrArg ((ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).map
        (rightTranspose hB' N i)).hom (extendScalars_hom_tmul _
          (rightGenTranspose (R := R) (R' := R') (B := B) (B' := B') N i) t m)).trans ?_
    refine (((ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).map
        (rightTranspose hB' N i)).hom.map_smul t _).trans ?_
    refine Eq.trans ?_ (congrArg (rightRestrictHom (R' := R') (B' := B') N i).hom
      (extendScalars_hom_tmul _ ((rightFlatHomologyIso hB' i).inv.app
        ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.obj N)) t m)).symm
    refine Eq.trans ?_ ((rightRestrictHom (R' := R') (B' := B') N i).hom.map_smul t _).symm
    rw [rightGenTranspose_one_tmul, rightTranspose_rightGen]

omit [Algebra R A'] [IsScalarTower R R' A'] [HasDerivedCategory.{u} (ModuleCat.{u} B')] in
theorem rightGen_apply (m : baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i) :
    (rightGen (R := R) (R' := R') (B := B) (B' := B') N i).hom m =
      (1 : A' ⊗[R'] B') ⊗ₜ[A' ⊗[R'] (R' ⊗[R] B), topHom R R' B A' B']
        (show baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i from m) :=
  rfl

omit [Algebra R A'] [IsScalarTower R R' A'] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
  [HasDerivedCategory.{u} (ModuleCat.{u} A')] [HasDerivedCategory.{u} (ModuleCat.{u} B')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))] in
theorem tensor_tmul_eq_topHom_mul (a' : A') (b' : B') :
    (a' ⊗ₜ[R'] b' : A' ⊗[R'] B') =
      topHom R R' B A' B' (Algebra.TensorProduct.includeLeft (R := R') (S := R') a') *
        includeRightRingHom R' A' B' b' := by
  rw [topHom_includeLeft]
  simp [Algebra.TensorProduct.tmul_mul_tmul, includeRightRingHom]

omit [Algebra R A'] [IsScalarTower R R' A'] [HasDerivedCategory.{u} (ModuleCat.{u} B')] in
theorem rightGenTranspose_surjective :
    Function.Surjective (rightGenTranspose (R := R) (R' := R') (B := B) (B' := B') N i).hom := by
  suffices h : ∀ x : (ModuleCat.extendScalars.{u, u, u} (topHom R R' B A' B')).obj
          (baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i),
      ∃ y, (rightGenTranspose (R := R) (R' := R') (B := B) (B' := B') N i).hom y = x from h
  intro x
  induction x using extendScalars_induction with
  | h0 => exact ⟨0, _root_.map_zero _⟩
  | hadd x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, (_root_.map_add _ a b).trans (congrArg₂ (· + ·) ha hb)⟩
  | htmul c m =>
    revert c
    suffices h : ∀ c : A' ⊗[R'] B', ∃ y,
        (rightGenTranspose (R := R) (R' := R') (B := B) (B' := B') N i).hom y =
          c ⊗ₜ[A' ⊗[R'] (R' ⊗[R] B), topHom R R' B A' B'] m from h
    intro c
    induction c using TensorProduct.induction_on with
    | zero => exact ⟨0, (_root_.map_zero _).trans
        (TensorProduct.zero_tmul (M := ↑((ModuleCat.restrictScalars.{u} (topHom R R' B A' B')).obj
            (ModuleCat.of (A' ⊗[R'] B') (A' ⊗[R'] B')))) m).symm⟩
    | add c c' hc hc' =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨b, hb⟩ := hc'
      exact ⟨a + b, (_root_.map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans
        (TensorProduct.add_tmul (M := ↑((ModuleCat.restrictScalars.{u} (topHom R R' B A' B')).obj
            (ModuleCat.of (A' ⊗[R'] B') (A' ⊗[R'] B')))) c c' m).symm)⟩
    | tmul a' b' =>
      exact ⟨b' ⊗ₜ[R' ⊗[R] B, (rightTensorHom R R' B B').toRingHom]
        (show baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i from
          ((Algebra.TensorProduct.includeLeft (R := R') (S := R') a' :
            A' ⊗[R'] (R' ⊗[R] B)) • m)),
        (extendScalars_hom_tmul _ (rightGenTranspose (R := R) (R' := R') (B := B) (B' := B') N i)
            b' _).trans
        ((congrArg (fun z : ((ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).obj
          ((ModuleCat.extendScalars.{u, u, u} (topHom R R' B A' B')).obj
          (baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i)) : Type u) => b' • z)
          ((rightGenTranspose_one_tmul (R := R) (R' := R') (B := B) (B' := B') N i _).trans
            (rightGen_apply (R := R) (R' := R') (B := B) (B' := B') N i _))).trans
        ((restrict_extendScalars_smul_one_tmul (topHom R R' B A' B')
            (includeRightRingHom R' A' B') b' _).trans
        ((TensorProduct.smul_tmul (R := A' ⊗[R'] (R' ⊗[R] B)) (M :=
            ↑((ModuleCat.restrictScalars.{u} (topHom R R' B A' B')).obj (ModuleCat.of (A' ⊗[R'] B')
                (A' ⊗[R'] B'))))
            (Algebra.TensorProduct.includeLeft (R := R') (S := R') a')
            (show ↑((ModuleCat.restrictScalars.{u} (topHom R R' B A' B')).obj (ModuleCat.of (A'
                ⊗[R'] B') (A' ⊗[R'] B'))) from includeRightRingHom R' A' B' b') m).symm.trans
          (congrArg (fun c : A' ⊗[R'] B' => c ⊗ₜ[A' ⊗[R'] (R' ⊗[R] B), topHom R R' B A' B'] m)
            (tensor_tmul_eq_topHom_mul (R := R) (R' := R') (B := B) a' b').symm))))⟩

omit [Algebra R A'] [IsScalarTower R R' A'] in
/-- **The comparison of the right-hand column is bijective.** -/
theorem rightTranspose_bijective : Function.Bijective (rightTranspose hB' N i).hom := by
  have hf : Function.Bijective
      (((rightFlatHomologyIso hB' i).inv.app
        ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.obj N)).hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hr : Function.Bijective (rightRestrictHom (R' := R') (B' := B') N i).hom :=
    ⟨fun x y h => h, fun y => ⟨y, rfl⟩⟩
  have hc := hr.comp hf
  have key := rightTranspose_rightGenTranspose hB' N i
  have hcomp : Function.Bijective
      (((ModuleCat.restrictScalars.{u} (includeRightRingHom R' A' B')).map
        (rightTranspose hB' N i)).hom ∘ (rightGenTranspose (R := R) (R' := R') (B := B)
            (B' := B') N i).hom) :=
    ⟨fun x y hxy => hc.1 ((key x).symm.trans (hxy.trans (key y))),
      fun z => let ⟨x, hx⟩ := hc.2 z; ⟨x, (key x).trans hx⟩⟩
  exact bijective_of_bijective_comp
    (rightGenTranspose_surjective (R := R) (R' := R') (B := B) (B' := B') N i) hcomp

instance isIso_rightTranspose : IsIso (rightTranspose hB' N i) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (rightTranspose_bijective hB' N i)

end Right


/-! ### The base row: flat base change of the base ring `R → R'` -/

section Base

variable [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
  [HasDerivedCategory.{u} (ModuleCat.{u} B)] [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))]

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
  [HasDerivedCategory.{u} (ModuleCat.{u} B)] [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))] in
theorem baseSquare_comm :
    (algebraMap R' (R' ⊗[R] B)).comp (algebraMap R R') =
      (includeRightRingHom R R' B).comp (algebraMap R B) := by
  ext r
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]

/-- The comparison of Stacks 065Z for the square `R → R'`, `R → B`, `R' → R' ⊗_R B`,
`B → R' ⊗_R B`: `(Y|_R) ⊗ᴸ_R B ⟶ (Y ⊗ᴸ_{R'} (R' ⊗_R B))|_B`, natural in `Y ∈ D(R')`. -/
def baseSquareComparison :
    (ModuleCat.restrictScalars.{u} (algebraMap R R')).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).functor ⋙
        (ModuleCat.restrictScalars.{u} (includeRightRingHom R R' B)).mapDerivedCategory :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, u, u, u, u} R R' B (R' ⊗[R] B) _ _ _ _ _ _ _ _
    (algebraMap R R') (algebraMap R B) (algebraMap R' (R' ⊗[R] B)) (includeRightRingHom R R' B)
    baseSquare_comm
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)).functor
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).functor
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)).comparison
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).comparison
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).isLeftDerived).2.1

/-- **The comparison of the base square is invertible**, `R → R'` being flat (Stacks 0661). -/
instance isIso_baseSquareComparison [Module.Flat R R'] :
    IsIso (baseSquareComparison (R := R) (R' := R') (B := B)) := by
  let : Algebra B (R' ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  have h := derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u, u, u, u, u, u}
    (R := R) (A := R') (R' := B) (A' := R' ⊗[R] B)
    (PseudoCoherence.torIndependent_of_flat (R := R) (A := R') (B := B))
  exact @h (totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)).functor
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).functor
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)).comparison
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).comparison
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).isLeftDerived

end Base

/-! ### The middle step: from the base `R` to the base `R'` -/

section Middle

variable [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
  [HasDerivedCategory.{u} (ModuleCat.{u} B)] [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))]
  (N : DerivedCategory (ModuleCat.{u} A')) (i : ℤ)

/-- `H^i((N|_R) ⊗ᴸ_R B) ⟶ H^i((N|_{R'}) ⊗ᴸ_{R'} (R' ⊗_R B))|_B`, as a map of `B`-modules. -/
def middleHom :
    baseChangeCohomologyOverBase (R := R) (R' := B) N i ⟶
      (ModuleCat.restrictScalars.{u} (includeRightRingHom R R' B)).obj
        (baseChangeCohomologyOverBase (R := R') (R' := R' ⊗[R] B) N i) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)).functor.map
        ((restrictScalarsTowerDerivedIso (R := R) (A := R') (A₂ := A')).inv.app N)) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
      ((baseSquareComparison (R := R) (R' := R') (B := B)).app
        ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.obj N)) ≫
    ((ModuleCat.restrictScalars.{u} (includeRightRingHom R R' B)).mapDerivedCategoryHomologyIso
      i).hom.app
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).functor.obj
        ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.obj N))

instance isIso_middleHom [Module.Flat R R'] :
    IsIso (middleHom (R := R) (R' := R') (B := B) N i) := by
  dsimp only [middleHom]
  infer_instance

/-- `middleHom` intertwines the actions of `A'` on the two sides. -/
theorem middleHom_comm (a' : A') :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)).functor.map
          ((ModuleCat.restrictScalars.{u} (algebraMap R A')).mapDerivedCategory.map
            (a' • 𝟙 N))) ≫
        middleHom (R := R) (R' := R') (B := B) N i =
      middleHom (R := R) (R' := R') (B := B) N i ≫
        (ModuleCat.restrictScalars.{u} (includeRightRingHom R R' B)).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R' ⊗[R] B)) i).map
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).functor.map
              ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.map
                (a' • 𝟙 N)))) := by
  have h1 := (restrictScalarsTowerDerivedIso (R := R) (A := R') (A₂ := A')).inv.naturality
    (a' • 𝟙 N)
  have h2 := (baseSquareComparison (R := R) (R' := R') (B := B)).naturality
    ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.map (a' • 𝟙 N))
  have h3 := ((ModuleCat.restrictScalars.{u} (includeRightRingHom R R'
      B)).mapDerivedCategoryHomologyIso
      i).hom.naturality
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R' (R' ⊗[R] B))).functor.map
      ((ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory.map (a' • 𝟙 N)))
  dsimp only [Functor.comp_map] at h1 h2 h3
  have e1 := congrArg (fun f => (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)).functor.map f)) h1
  have e2 := congrArg (fun f => (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map f) h2
  simp only [Functor.map_comp] at e1 e2
  dsimp only [middleHom]
  rw [reassoc_of% e1, reassoc_of% e2, h3]
  simp only [Category.assoc]

end Middle

/-! ### The left-hand column: flat base change along `A → A'` -/

section Left

variable [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} B)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))]
  (M : DerivedCategory (ModuleCat.{u} A)) (i : ℤ)

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} B)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))] in
theorem midHom_includeLeft (a : A) :
    midHom R R' A B A' (Algebra.TensorProduct.includeLeft (R := R) (S := R) a) =
      Algebra.TensorProduct.includeLeft (R := R') (S := R') (algebraMap A A' a) := by
  simp [midHom, TorChangeOfRings.tensorProductMap, Algebra.TensorProduct.one_def]

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} B)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))] in
theorem midHom_includeRight (b : B) :
    midHom R R' A B A' (Algebra.TensorProduct.includeRight b) =
      Algebra.TensorProduct.includeRight (includeRightRingHom R R' B b) := by
  simp [midHom, TorChangeOfRings.tensorProductMap, Algebra.TensorProduct.one_def]

/-- `middleHom` is equivariant for the left tensor factor `A'`. -/
theorem middleHom_includeLeft_smul (N : DerivedCategory (ModuleCat.{u} A')) (a' : A')
    (z : baseChangeCohomology (R := R) (R' := B) N i) :
    (middleHom (R := R) (R' := R') (B := B) N i).hom
        ((Algebra.TensorProduct.includeLeft (R := R) (S := R) a' : A' ⊗[R] B) • z) =
      ((Algebra.TensorProduct.includeLeft (R := R') (S := R') a' : A' ⊗[R'] (R' ⊗[R] B)) •
        (show baseChangeCohomology (R := R') (R' := R' ⊗[R] B) N i from
          (middleHom (R := R) (R' := R') (B := B) N i).hom z)) :=
  (congrArg (middleHom (R := R) (R' := R') (B := B) N i).hom
    (baseChangeCohomology_includeLeft_smul (R := R) (R' := B) N i a' z)).trans
  ((DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
      (middleHom_comm (R := R) (R' := R') (B := B) N i a'))
      (show baseChangeCohomologyOverBase (R := R) (R' := B) N i from z)).trans
    (baseChangeCohomology_includeLeft_smul (R := R') (R' := R' ⊗[R] B) N i a'
      ((middleHom (R := R) (R' := R') (B := B) N i).hom z)).symm)

/-- The unit of derived extension of scalars along `A → A'` followed by `middleHom`, as an
additive map. -/
def leftComparisonAdd :
    (baseChangeCohomology (R := R) (R' := B) M i : Type u) →+
      ((ModuleCat.restrictScalars.{u} (midHom R R' A B A')).obj
        (baseChangeCohomology (R := R') (R' := R' ⊗[R] B)
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i) :
        Type u) where
  toFun m := (middleHom (R := R) (R' := R') (B := B)
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i).hom
      (((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A') (R' := B) i).app M).hom m)
  map_zero' := (congrArg (middleHom (R := R) (R' := R') (B := B)
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i).hom
      ((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A') (R' := B) i).app
        M).hom.map_zero).trans (_root_.map_zero _)
  map_add' x y := (congrArg (middleHom (R := R) (R' := R') (B := B)
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i).hom
      (((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A') (R' := B) i).app
        M).hom.map_add x y)).trans (_root_.map_add _ _ _)

/-- The unit of derived extension of scalars along `A → A'` followed by `middleHom`, as a map of
`A ⊗_R B`-modules into the restriction of the cohomology over `R'`. -/
def leftComparison :
    baseChangeCohomology (R := R) (R' := B) M i ⟶
      (ModuleCat.restrictScalars.{u} (midHom R R' A B A')).obj
        (baseChangeCohomology (R := R') (R' := R' ⊗[R] B)
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i) :=
  ModuleCat.ofHom
    (X := (baseChangeCohomology (R := R) (R' := B) M i : Type u))
    (Y := ((ModuleCat.restrictScalars.{u} (midHom R R' A B A')).obj
        (baseChangeCohomology (R := R') (R' := R' ⊗[R] B)
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i) : Type u))
    (tensorLinearMapOfIncludes (R := R) (A := A) (S := B) (leftComparisonAdd (R := R) (R' := R') (B
        := B) (A' := A') M i)
      (fun a m =>
        (congrArg (middleHom (R := R) (R' := R') (B := B)
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i).hom
          (((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A') (R' := B) i).app
            M).hom.map_smul a m)).trans
        ((middleHom_includeLeft_smul (R := R) (R' := R') (B := B) i
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M)
          (algebraMap A A' a) _).trans
          (congrArg (fun z => z • (show baseChangeCohomology (R := R') (R' := R' ⊗[R] B)
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i from
              leftComparisonAdd (R := R) (R' := R') (B := B)
                  (A' := A') M i m)) (midHom_includeLeft a).symm)))
      (fun b m =>
        (congrArg (middleHom (R := R) (R' := R') (B := B)
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i).hom
          ((baseChangeCohomologyUnitNatTrans_app_includeRight_smul (R := R) (A := A) (A₂ := A')
            (R' := B) i M b m).trans
            (baseChangeCohomology_includeRight_smul (R := R) (R' := B)
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i b
              _))).trans
        (((middleHom (R := R) (R' := R') (B := B)
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M)
              i).hom.map_smul
            b _).trans
        ((baseChangeCohomology_includeRight_smul (R := R') (R' := R' ⊗[R] B)
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i
            (includeRightRingHom R R' B b) (leftComparisonAdd (R := R) (R' := R') (B := B)
                (A' := A') M i m)).symm.trans
          (congrArg (fun z => z • (show baseChangeCohomology (R := R') (R' := R' ⊗[R] B)
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i from
              leftComparisonAdd (R := R) (R' := R') (B := B)
                  (A' := A') M i m)) (midHom_includeRight b).symm)))))

/-- The comparison `(A' ⊗_{R'} (R' ⊗_R B)) ⊗_{A ⊗_R B} H ⟶ H₁` of the left-hand column. -/
def leftTranspose :
    (ModuleCat.extendScalars.{u, u, u} (midHom R R' A B A')).obj
        (baseChangeCohomology (R := R) (R' := B) M i) ⟶
      baseChangeCohomology (R := R') (R' := R' ⊗[R] B)
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i :=
  ModuleCat.extendScalarsTranspose _ (leftComparison (R := R) (R' := R') (B := B) (A' := A') M i)

/-- `m ↦ 1 ⊗ m`, as a map of `A`-modules. -/
def leftGen :
    (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A B)).obj
        (baseChangeCohomology (R := R) (R' := B) M i) ⟶
      (ModuleCat.restrictScalars.{u} (algebraMap A A')).obj
        ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R] B))).obj
          ((ModuleCat.extendScalars.{u, u, u} (midHom R R' A B A')).obj
            (baseChangeCohomology (R := R) (R' := B) M i))) :=
  ModuleCat.ofHom
    (X := ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A B)).obj
        (baseChangeCohomology (R := R) (R' := B) M i) : Type u))
    (Y := ((ModuleCat.restrictScalars.{u} (algebraMap A A')).obj
        ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R] B))).obj
          ((ModuleCat.extendScalars.{u, u, u} (midHom R R' A B A')).obj
            (baseChangeCohomology (R := R) (R' := B) M i))) : Type u))
    { toFun := fun m => (1 : A' ⊗[R'] (R' ⊗[R] B)) ⊗ₜ[A ⊗[R] B, midHom R R' A B A']
        (show baseChangeCohomology (R := R) (R' := B) M i from m)
      map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
      map_smul' := fun a m =>
        (extendScalars_one_tmul_smul (midHom R R' A B A')
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) a) _).trans
          (congrArg (fun z => z • (show (ModuleCat.extendScalars.{u, u, u}
            (midHom R R' A B A')).obj (baseChangeCohomology (R := R) (R' := B) M i) from
            (1 : A' ⊗[R'] (R' ⊗[R] B)) ⊗ₜ[A ⊗[R] B, midHom R R' A B A'] m))
            (midHom_includeLeft a)) }

/-- The `A'`-linear map `A' ⊗_A H ⟶ (A' ⊗_{R'} (R' ⊗_R B)) ⊗_{A ⊗_R B} H`. -/
def leftGenTranspose :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A A')).obj
        ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A B)).obj
          (baseChangeCohomology (R := R) (R' := B) M i)) ⟶
      (ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R] B))).obj
        ((ModuleCat.extendScalars.{u, u, u} (midHom R R' A B A')).obj
          (baseChangeCohomology (R := R) (R' := B) M i)) :=
  ModuleCat.extendScalarsTranspose _ (leftGen (R := R) (R' := R') (B := B) (A' := A') M i)

/-- `middleHom` as a map of `A'`-modules. -/
def middleLeftHom :
    (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A' B)).obj
        (baseChangeCohomology (R := R) (R' := B)
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i) ⟶
      (ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R] B))).obj
        (baseChangeCohomology (R := R') (R' := R' ⊗[R] B)
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i) :=
  ModuleCat.ofHom
    (X := ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A' B)).obj
        (baseChangeCohomology (R := R) (R' := B)
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i) : Type u))
    (Y := ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R] B))).obj
        (baseChangeCohomology (R := R') (R' := R' ⊗[R] B)
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i) : Type u))
    { toFun := fun z => (middleHom (R := R) (R' := R') (B := B)
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i).hom z
      map_add' := fun _ _ => _root_.map_add _ _ _
      map_smul' := fun a' z => middleHom_includeLeft_smul (R := R) (R' := R') (B := B) i
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) a' z }

theorem leftTranspose_one_tmul (m : baseChangeCohomology (R := R) (R' := B) M i) :
    (leftTranspose (R := R) (R' := R') (B := B) (A' := A') M i).hom
        ((1 : A' ⊗[R'] (R' ⊗[R] B)) ⊗ₜ[A ⊗[R] B, midHom R R' A B A'] m) =
      (leftComparison (R := R) (R' := R') (B := B) (A' := A') M i).hom m :=
  ModuleCat.extendScalarsTranspose_one_tmul _ _ m

omit [HasDerivedCategory.{u} (ModuleCat.{u} R')] [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))] in
theorem leftGenTranspose_one_tmul
    (m : (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A B)).obj
      (baseChangeCohomology (R := R) (R' := B) M i)) :
    (leftGenTranspose (R := R) (R' := R') (B := B) (A' := A') M i).hom ((1 : A') ⊗ₜ[A, algebraMap A
        A'] m) =
      (leftGen (R := R) (R' := R') (B := B) (A' := A') M i).hom m :=
  ModuleCat.extendScalarsTranspose_one_tmul _ _ m

theorem localizedComparison_one_tmul
    (m : (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A B)).obj
      (baseChangeCohomology (R := R) (R' := B) M i)) :
    ((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A') (R' := B) i).app
        M).hom ((1 : A') ⊗ₜ[A, algebraMap A A'] m) =
      ((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A') (R' := B) i).app M).hom m :=
  ModuleCat.extendScalarsTranspose_one_tmul _ _ m

theorem leftTranspose_leftGen
    (m : (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A B)).obj
      (baseChangeCohomology (R := R) (R' := B) M i)) :
    ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R] B))).map
        (leftTranspose (R := R) (R' := R') (B := B) (A' := A') M i)).hom ((leftGen (R := R)
            (R' := R') (B := B) (A' := A') M i).hom m) =
      (middleLeftHom (R := R) (R' := R') (B := B) (A' := A') M i).hom
        (((baseChangeCohomologyUnitNatTrans (R := R) (A := A) (A₂ := A') (R' := B) i).app
          M).hom m) :=
  leftTranspose_one_tmul (R := R) (R' := R') (B := B) (A' := A') M i m

theorem leftTranspose_leftGenTranspose
    (x : (ModuleCat.extendScalars.{u, u, u} (algebraMap A A')).obj
        ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R A B)).obj
          (baseChangeCohomology (R := R) (R' := B) M i))) :
    ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R] B))).map
        (leftTranspose (R := R) (R' := R') (B := B) (A' := A') M i)).hom ((leftGenTranspose
            (R := R) (R' := R') (B := B) (A' := A') M i).hom x) =
      (middleLeftHom (R := R) (R' := R') (B := B) (A' := A') M i).hom
        (((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A') (R' := B)
          i).app M).hom x) := by
  induction x using extendScalars_induction with
  | h0 =>
    have hl := (leftGenTranspose (R := R) (R' := R') (B := B) (A' := A') M i).hom.map_zero
    have hr := ((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A') (R' := B)
      i).app M).hom.map_zero
    exact ((congrArg ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R] B))).map
        (leftTranspose (R := R) (R' := R') (B := B) (A' := A') M i)).hom hl).trans
        (_root_.map_zero _)).trans
      ((congrArg (middleLeftHom (R := R) (R' := R') (B := B) (A' := A') M i).hom hr).trans
        (_root_.map_zero _)).symm
  | hadd x y hx hy =>
    have hl := (leftGenTranspose (R := R) (R' := R') (B := B) (A' := A') M i).hom.map_add x y
    have hr := ((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A') (R' := B)
      i).app M).hom.map_add x y
    exact ((congrArg ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R] B))).map
        (leftTranspose (R := R) (R' := R') (B := B) (A' := A') M i)).hom hl).trans
        (_root_.map_add _ _ _)).trans
      ((congrArg₂ (· + ·) hx hy).trans
        ((congrArg (middleLeftHom (R := R) (R' := R') (B := B) (A' := A') M i).hom hr).trans
          (_root_.map_add _ _ _)).symm)
  | htmul t m =>
    refine (congrArg ((ModuleCat.restrictScalars.{u}
        (includeLeftRingHom R' A' (R' ⊗[R] B))).map (leftTranspose (R := R) (R' := R') (B := B) (A'
            := A') M i)).hom
      (extendScalars_hom_tmul _ (leftGenTranspose (R := R) (R' := R') (B := B) (A' := A') M i) t
          m)).trans ?_
    refine (((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R] B))).map
        (leftTranspose (R := R) (R' := R') (B := B) (A' := A') M i)).hom.map_smul t _).trans ?_
    refine Eq.trans ?_ (congrArg (middleLeftHom (R := R) (R' := R') (B := B) (A' := A') M i).hom
      (extendScalars_hom_tmul _ ((localizedBaseChangeCohomologyComparison (R := R) (A := A)
        (A₂ := A') (R' := B) i).app M) t m)).symm
    refine Eq.trans ?_ ((middleLeftHom (R := R) (R' := R') (B := B) (A' := A') M i).hom.map_smul t
        _).symm
    rw [leftGenTranspose_one_tmul, leftTranspose_leftGen]
    exact congrArg (fun z : ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R]
        B))).obj
          (baseChangeCohomology (R := R') (R' := R' ⊗[R] B)
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj
                M) i) : Type u) => t • z)
      (congrArg (middleLeftHom (R := R) (R' := R') (B := B) (A' := A') M i).hom
          (localizedComparison_one_tmul (R := R) (B := B) (A' := A') M i m).symm)

omit [HasDerivedCategory.{u} (ModuleCat.{u} R')] [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))] in
theorem leftGen_apply
    (m : (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A B)).obj
      (baseChangeCohomology (R := R) (R' := B) M i)) :
    (leftGen (R := R) (R' := R') (B := B) (A' := A') M i).hom m =
      (1 : A' ⊗[R'] (R' ⊗[R] B)) ⊗ₜ[A ⊗[R] B, midHom R R' A B A']
        (show baseChangeCohomology (R := R) (R' := B) M i from m) :=
  rfl

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} B)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))] in
theorem d1_tmul_eq (a' : A') (r' : R') (b : B) :
    (a' ⊗ₜ[R'] (r' ⊗ₜ[R] b) : A' ⊗[R'] (R' ⊗[R] B)) =
      midHom R R' A B A' (Algebra.TensorProduct.includeRight b) *
        includeLeftRingHom R' A' (R' ⊗[R] B) (algebraMap R' A' r' * a') := by
  rw [midHom_includeRight]
  have : (r' ⊗ₜ[R] b : R' ⊗[R] B) = r' • ((1 : R') ⊗ₜ[R] b) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, ← TensorProduct.smul_tmul, Algebra.smul_def]
  simp [Algebra.TensorProduct.tmul_mul_tmul, includeRightRingHom, includeLeftRingHom]

omit [HasDerivedCategory.{u} (ModuleCat.{u} R')] [HasDerivedCategory.{u} (ModuleCat.{u} A')]
  [HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B))] in
theorem leftGenTranspose_surjective :
    Function.Surjective (leftGenTranspose (R := R) (R' := R') (B := B) (A' := A') M i).hom := by
  suffices h : ∀ x : (ModuleCat.extendScalars.{u, u, u} (midHom R R' A B A')).obj
          (baseChangeCohomology (R := R) (R' := B) M i),
      ∃ y, (leftGenTranspose (R := R) (R' := R') (B := B) (A' := A') M i).hom y = x from h
  intro x
  induction x using extendScalars_induction with
  | h0 => exact ⟨0, _root_.map_zero _⟩
  | hadd x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, (_root_.map_add _ a b).trans (congrArg₂ (· + ·) ha hb)⟩
  | htmul d m =>
    revert d
    suffices h : ∀ d : A' ⊗[R'] (R' ⊗[R] B), ∃ y,
        (leftGenTranspose (R := R) (R' := R') (B := B) (A' := A') M i).hom y = d ⊗ₜ[A ⊗[R] B,
            midHom R R' A B A'] m from h
    intro d
    induction d using TensorProduct.induction_on with
    | zero => exact ⟨0, (_root_.map_zero _).trans
        (TensorProduct.zero_tmul (M := ↑((ModuleCat.restrictScalars.{u} (midHom R R' A B A')).obj
            (ModuleCat.of (A' ⊗[R'] (R' ⊗[R] B)) (A' ⊗[R'] (R' ⊗[R] B))))) m).symm⟩
    | add c c' hc hc' =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨b, hb⟩ := hc'
      exact ⟨a + b, (_root_.map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans
        (TensorProduct.add_tmul (M := ↑((ModuleCat.restrictScalars.{u} (midHom R R' A B A')).obj
            (ModuleCat.of (A' ⊗[R'] (R' ⊗[R] B)) (A' ⊗[R'] (R' ⊗[R] B))))) c c' m).symm)⟩
    | tmul a' β =>
      induction β using TensorProduct.induction_on with
      | zero =>
        exact ⟨0, (_root_.map_zero _).trans
          ((TensorProduct.zero_tmul (M := ↑((ModuleCat.restrictScalars.{u} (midHom R R' A B A')).obj
            (ModuleCat.of (A' ⊗[R'] (R' ⊗[R] B)) (A' ⊗[R'] (R' ⊗[R] B))))) m).symm.trans
            (congrArg (fun c : A' ⊗[R'] (R' ⊗[R] B) => c ⊗ₜ[A ⊗[R] B, midHom R R' A B A'] m)
              (TensorProduct.tmul_zero _ a').symm))⟩
      | add β β' hβ hβ' =>
        obtain ⟨a, ha⟩ := hβ
        obtain ⟨b, hb⟩ := hβ'
        exact ⟨a + b, (_root_.map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans
          ((TensorProduct.add_tmul (M := ↑((ModuleCat.restrictScalars.{u} (midHom R R' A B A')).obj
            (ModuleCat.of (A' ⊗[R'] (R' ⊗[R] B)) (A' ⊗[R'] (R' ⊗[R] B))))) _ _ m).symm.trans
            (congrArg (fun c : A' ⊗[R'] (R' ⊗[R] B) => c ⊗ₜ[A ⊗[R] B, midHom R R' A B A'] m)
              (TensorProduct.tmul_add a' β β').symm)))⟩
      | tmul r' b =>
        exact ⟨(algebraMap R' A' r' * a') ⊗ₜ[A, algebraMap A A']
          (show (ModuleCat.restrictScalars.{u} (includeLeftRingHom R A B)).obj
            (baseChangeCohomology (R := R) (R' := B) M i) from
            ((Algebra.TensorProduct.includeRight b : A ⊗[R] B) • m)),
          (extendScalars_hom_tmul _ (leftGenTranspose (R := R) (R' := R') (B := B) (A' := A') M i)
              _ _).trans
          ((congrArg (fun z : ((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R' ⊗[R]
              B))).obj
          ((ModuleCat.extendScalars.{u, u, u} (midHom R R' A B A')).obj
          (baseChangeCohomology (R := R) (R' := B) M
              i)) : Type u) => (algebraMap R' A' r' * a') • z)
            ((leftGenTranspose_one_tmul (R := R) (R' := R') (B := B) (A' := A') M i _).trans
              (leftGen_apply (R := R) (R' := R') (B := B) (A' := A') M i _))).trans
          ((restrict_extendScalars_smul_one_tmul (midHom R R' A B A')
              (includeLeftRingHom R' A' (R' ⊗[R] B)) (algebraMap R' A' r' * a') _).trans
          ((TensorProduct.smul_tmul (R := A ⊗[R] B) (M := ↑((ModuleCat.restrictScalars.{u} (midHom
              R R' A B A')).obj
            (ModuleCat.of (A' ⊗[R'] (R' ⊗[R] B)) (A' ⊗[R'] (R' ⊗[R] B)))))
              (Algebra.TensorProduct.includeRight b)
              (show ↑((ModuleCat.restrictScalars.{u} (midHom R R' A B A')).obj
            (ModuleCat.of (A' ⊗[R'] (R' ⊗[R] B)) (A' ⊗[R'] (R' ⊗[R] B)))) from
                includeLeftRingHom R' A' (R' ⊗[R] B) (algebraMap R' A' r' * a')) m).symm.trans
            (congrArg (fun c : A' ⊗[R'] (R' ⊗[R] B) =>
                c ⊗ₜ[A ⊗[R] B, midHom R R' A B A'] m)
              (d1_tmul_eq (R := R) (A := A) a' r' b).symm))))⟩

/-- **The comparison of the left-hand column is bijective**, `A → A'` being flat. -/
theorem leftTranspose_bijective [Module.Flat R R'] (hA : (algebraMap A A').Flat) :
    Function.Bijective (leftTranspose (R := R) (R' := R') (B := B) (A' := A') M i).hom := by
  have := isIso_localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ := A') (R' := B)
    hA i
  have hc : Function.Bijective ((localizedBaseChangeCohomologyComparison (R := R) (A := A) (A₂ :=
      A') (R' := B) i).app M).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hm : Function.Bijective (middleLeftHom (R := R) (R' := R') (B := B) (A' := A') M i).hom :=
    (ConcreteCategory.isIso_iff_bijective (middleHom (R := R) (R' := R') (B := B)
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i)).mp
      inferInstance
  have hmc := hm.comp hc
  have key := leftTranspose_leftGenTranspose (R := R) (R' := R') (B := B) (A' := A') M i
  have hcomp : Function.Bijective (((ModuleCat.restrictScalars.{u} (includeLeftRingHom R' A' (R'
      ⊗[R] B))).map
        (leftTranspose (R := R) (R' := R') (B := B) (A' := A') M i)).hom ∘ (leftGenTranspose
            (R := R) (R' := R') (B := B) (A' := A') M i).hom) :=
    ⟨fun x y hxy => hmc.1 ((key x).symm.trans (hxy.trans (key y))),
      fun z => let ⟨x, hx⟩ := hmc.2 z; ⟨x, (key x).trans hx⟩⟩
  exact bijective_of_bijective_comp (leftGenTranspose_surjective (R := R) (R' := R') (B := B) (A'
      := A') M i) hcomp

end Left

end FlatSquare

open FlatSquare in
/-- **Stacks 0DJD.** Consider a commutative diagram of rings
`A' ← R' → B'` over `A ← R → B`, with `R'` flat over `R`, `A'` flat over `A ⊗_R R'` and `B'` flat
over `R' ⊗_R B` (the assumptions of Stacks 08HW). For `M ∈ D(A)` there is a canonical
isomorphism of `A' ⊗_{R'} B'`-modules

`H^i((M ⊗ᴸ_A A') ⊗ᴸ_{R'} B') ≅ H^i(M ⊗ᴸ_R B) ⊗_{A ⊗_R B} (A' ⊗_{R'} B')`.

The derived tensor products are the ones of the source: `M ⊗ᴸ_A A'` is read in `D(R')` and
base changed along `R' → B'`, and `M` is read in `D(R)` and base changed along `R → B`; the
module structures over `A' ⊗_{R'} B'` and `A ⊗_R B` on the cohomology are those of
`RingTheory.TorIndependence.baseChangeCohomology`, coming from the actions of `A'` and of `A` by
endomorphisms. Extension of scalars puts the new ring on the left of the tensor product. -/
@[stacks 0DJD]
def baseChangeCohomologyIsoOfFlat
    {R R' A B A' B' : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B']
    [Algebra R R'] [Algebra R A] [Algebra R B]
    [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [Algebra R' A'] [IsScalarTower R R' A']
    [Algebra B B'] [Algebra R B'] [IsScalarTower R B B'] [Algebra R' B'] [IsScalarTower R R' B']
    [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} R')]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} B)]
    [HasDerivedCategory.{u} (ModuleCat.{u} A')] [HasDerivedCategory.{u} (ModuleCat.{u} B')]
    (hR' : (algebraMap R R').Flat)
    (hA' : (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A A')
      (IsScalarTower.toAlgHom R R' A') (fun _ _ ↦ Commute.all _ _)).toRingHom.Flat)
    (hB' : (Algebra.TensorProduct.lift (Algebra.ofId R' B') (IsScalarTower.toAlgHom R B B')
      (fun _ _ ↦ Commute.all _ _)).toRingHom.Flat)
    (M : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    baseChangeCohomology (R := R') (R' := B')
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i ≅
      (ModuleCat.extendScalars.{u, u, u}
        (TorChangeOfRings.tensorProductMap R R' A B A' B' (IsScalarTower.toAlgHom R A A')
          (IsScalarTower.toAlgHom R B B'))).obj
        (baseChangeCohomology (R := R) (R' := B) M i) :=
  letI : HasDerivedCategory.{u} (ModuleCat.{u} (R' ⊗[R] B)) := ModuleCat.hasDerivedCategory
  haveI : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hR'
  haveI := isIso_rightTranspose (R := R) (B := B) hB'
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i
  haveI : IsIso (leftTranspose (R := R) (R' := R') (B := B) (A' := A') M i) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (leftTranspose_bijective (R := R) (R' := R') (B := B) (A' := A') M i
        (flat_algebraMap_left hR' hA'))
  (asIso (rightTranspose (R := R) (B := B) hB'
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj M) i)).symm ≪≫
    (ModuleCat.extendScalars.{u, u, u} (topHom R R' B A' B')).mapIso
      (asIso (leftTranspose (R := R) (R' := R') (B := B) (A' := A') M i)).symm ≪≫
    (ModuleCat.extendScalarsComp (midHom R R' A B A') (topHom R R' B A' B')).symm.app _ ≪≫
    eqToIso (congrArg (fun φ : A ⊗[R] B →+* A' ⊗[R'] B' =>
      (ModuleCat.extendScalars.{u, u, u} φ).obj (baseChangeCohomology (R := R) (R' := B) M i))
      (topHom_comp_midHom (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')))

end RingTheory.TorIndependence

end
