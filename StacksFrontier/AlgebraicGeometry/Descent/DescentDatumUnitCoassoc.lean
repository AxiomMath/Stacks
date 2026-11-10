module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumResidueInvariants

/-!
# The coassociativity obligation of Stacks 0APK, reduced to a cocycle diagram of rings

Step 4 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) descends the
ring of functions on an invariant subset `E` of the scheme `V` of a descent datum along the
faithfully flat `Γ(S, ⊤) ⟶ Γ(X, ⊤)`. The algebraic input it needs beyond the two instances of
Stacks 0APJ is **coassociativity of the unit** of the transition isomorphism `ψ`, which the
source performs with "details omitted"; it is the hypothesis `hkey` of
`ModuleCat.bijective_productMap_descentInvariants_of_isPushout`, of
`AlgebraicGeometry.DescentDatum.isPushout_descentInvariants_of_cocycle` and of
`AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_legs_of_restrictOpen`.

That hypothesis is an identity in `A ⊗_R (A ⊗_R C)` between two maps built from the unit, and no
geometric statement bears on it directly. This file converts it into data of the shape geometry
produces: **a third pushout square**, presenting a ring `Q₃` as `A ⊗_R Q` for `Q` the apex of the
second instance of Stacks 0APJ, **two morphisms `Λ, Λ' : Q ⟶ Q₃`** pinned down on the two legs of
that square, and the single equation `ς ≫ Λ = ς ≫ Λ'` between their composites with the coaction
`ς`. Geometrically `Q₃` is the ring of functions on `X ×_S (X ×_S E)`, the two morphisms are
restriction along `(x₁, v, x₂) ↦ (x₂, x₁ · v)` and along `(x₁, v, x₂) ↦ (x₂, v)`, and the
equation is the cocycle condition `x₂ · (x₁ · v) = x₂ · v` of the descent datum.  Note the
coordinate order: `Q₃`'s scheme is `(X ×_S V) ×_S X`, so the *new* `X` coordinate is written
*last*, and it is that one which the two morphisms preserve.

Exactly the same conversion, for a transition isomorphism *produced* from a coaction rather than
for one named by two pushout squares, is
`AlgebraicGeometry.exists_transition_unitCoassoc_of_isPushout`, which is how the single-chart case
of Stacks 0245 obtains its cocycle condition from
`AlgebraicGeometry.Space.descentAction_assoc`. See the implementation notes.

## Main results

* `ModuleCat.unitCoassoc_of_cocycle` : **the algebraic core.** For a pushout
  square presenting `Q` as `A ⊗_R C`, a pushout square presenting `Q₃` as `A ⊗_R Q`, a coaction
  `ς : C ⟶ Q` which is the identity on `A`, and two morphisms `Λ, Λ' : Q ⟶ Q₃` as above whose
  composites with `ς` agree, the unit `c ↦ ς c` read in `A ⊗_R C` is coassociative.
* `ModuleCat.unitCoassoc_algebraTransitionOfPushout` : the same for the unit of
  `ModuleCat.algebraTransitionOfPushout`, i.e. **the hypothesis `hkey` of step 4
  of the proof of Stacks 0APK, discharged from the cocycle diagram.**
* `ModuleCat.isPushout_descentInvariants_of_cocycleDiagram` : step 4 itself from
  the cocycle diagram — `C` is the base change to `A` of the subalgebra of `ψ`-invariants.
* `ModuleCat.exists_cocycleDiagram_of_algebra` : **the inhabitation witness.**
  For `C = A` and the canonical tensor-product squares the whole package exists, so the hypotheses
  of the three results above are jointly satisfiable and none of them is vacuous.
* `AlgebraicGeometry.DescentDatum.isPushout_algebraMap_transitionTargetBaseChange` : **the third
  instance of Stacks 0APJ**, presenting `Γ(X ×_S (X ×_S E), 𝒪)` as
  `Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(X ×_S E, 𝒪)`. This is the pushout square the cocycle diagram asks for, so
  what the diagram still owes is only the two morphisms and the cocycle identity.
* `AlgebraicGeometry.DescentDatum.unitCoassoc_descentAlgebraTransition` : the cocycle diagram
  written out for the two instances of Stacks 0APJ of the proof of Stacks 0APK, delivering `hkey`
  for `AlgebraicGeometry.DescentDatum.descentAlgebraTransition`.
* `AlgebraicGeometry.DescentDatum.isEffective_of_cocycleDiagram_of_legs_of_restrictOpen` :
  **the residue of Stacks 0APK over an affine base with `hkey` replaced by the cocycle diagram.**
  This is `AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_legs_of_restrictOpen` with
  its first obligation traded for one stated about rings of functions on fibre products.

## Implementation notes

*What this is not.* It is not a proof of Stacks 0APK and carries no tag. The cocycle diagram is a
hypothesis here, exactly as `hkey` was; what is established is that the diagram suffices, and that
the diagram is the form the geometry of the source's step 4 produces.

*Why the diagram and not the identity.* The two sides of `hkey` are
`LinearMap.lTensor A σ` and `LinearMap.lTensor A (TensorProduct.mk R A C 1)` applied to `σ c`.
Through the comparison of `Q₃` with `A ⊗_R (A ⊗_R C)` those two linear maps become the two ring
morphisms `Λ` and `Λ'`, which are determined by their restrictions to the two legs `kA` and `kC`
of the second square — and that is all four of the equations `hΛ₁`, `hΛ₂`, `hΛ₁'`, `hΛ₂'` say. So
the identity in the triple tensor product is equivalent to one equation between morphisms out of
`Q`, and that equation is a statement about maps of fibre products.

*Relation to `AlgebraicGeometry.exists_transition_unitCoassoc_of_isPushout`.* That theorem proves
the same coassociativity, from the same three pushout squares and the same cocycle identity, for a
transition isomorphism it *builds* from the coaction by `Algebra.TensorProduct.lift`; its
conclusion is existentially quantified, so a consumer which has already named its transition — as
the proof of Stacks 0APK has, through the two instances of Stacks 0APJ — cannot use it. The
coassociativity condition depends on the transition only through its unit, which is why
`ModuleCat.unitCoassoc_of_cocycle` is stated for the unit alone and takes the
linear map as an argument together with the equation identifying it: both the named transition of
this file and the built transition of that one satisfy that equation. Folding that theorem's
second conclusion onto this core is not done here, because its home
module does not import
`StacksFrontier.AlgebraicGeometry.Descent.Modules.AlgebraDescentFromPushout`.

*What remains for Stacks 0APK.* Three obligations, all geometric. The first is the cocycle diagram
of this file, of whose three parts the pushout square is proved here as
`AlgebraicGeometry.DescentDatum.isPushout_algebraMap_transitionTargetBaseChange`, so that what is
owed is the two restriction morphisms
`Γ(X ×_S E, 𝒪) ⟶ Γ(X ×_S (X ×_S E), 𝒪)` along `(x₁, x₂, v) ↦ (x₁, x₂ · v)` and along
`(x₁, x₂, v) ↦ (x₁, v)`, their four compatibilities with the legs of that square, and the cocycle
identity — for which
`AlgebraicGeometry.cocycle_iff_gluingAction_act_act` is the generalized-point form of
the datum's own cocycle condition. The second is the legs condition `hlegs` and the third is
Stacks 0AP4 as `hglueing`.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace ModuleCat

variable {R A C : Type u} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra A C]
    [Algebra R C] [IsScalarTower R A C] {P Q Q₃ : CommRingCat.{u}}
    {iC : CommRingCat.of C ⟶ P} {iA : CommRingCat.of A ⟶ P}
    {kA : CommRingCat.of A ⟶ Q} {kC : CommRingCat.of C ⟶ Q}
    {i₃ : CommRingCat.of A ⟶ Q₃} {j₃ : Q ⟶ Q₃}

/-- Two equal morphisms of commutative rings agree on every element. -/
private theorem ringHom_congr_apply {Y Z : CommRingCat.{u}} {g g' : Y ⟶ Z} (h : g = g') (y : Y) :
    g.hom y = g'.hom y := by rw [h]

/-- **The algebraic core of the coassociativity obligation of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK).**  Let `R → A → C` be a tower of
commutative rings, let `hQ` present `Q` as `A ⊗[R] C` and let `hQ₃` present `Q₃` as `A ⊗[R] Q`.
Let `ς : C ⟶ Q` be a coaction which restricts to the first leg of `hQ` on `A`, and let
`Λ, Λ' : Q ⟶ Q₃` be the two morphisms with `Λ` the identity on the `A`-leg and `ς` followed by the
`Q`-leg on the `C`-leg, and `Λ'` the identity on the `A`-leg and the `Q`-leg on the `C`-leg.  If
`ς ≫ Λ = ς ≫ Λ'` then the unit `u : C →ₗ[R] A ⊗[R] C` that `ς` induces is coassociative.

In the tensor-product picture `Λ` is `id ⊗ u` and `Λ'` is `id ⊗ (1 ⊗ ·)`, and the hypothesis
`hcoc` is the cocycle condition.  The unit is taken as an argument, with the equation `hu` pinning
it down, so that the result applies to any transition isomorphism whose unit is `ς`. -/
theorem unitCoassoc_of_cocycle
    (hQ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R C)) kA kC)
    (hQ₃ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R A) ≫ kA) i₃ j₃)
    (ς : CommRingCat.of C ⟶ Q)
    (hς : ∀ a : A, ς.hom (algebraMap A C a) = kA.hom a)
    {Λ Λ' : Q ⟶ Q₃}
    (hΛ₁ : kA ≫ Λ = i₃) (hΛ₂ : kC ≫ Λ = ς ≫ j₃)
    (hΛ₁' : kA ≫ Λ' = i₃) (hΛ₂' : kC ≫ Λ' = kC ≫ j₃)
    (hcoc : ς ≫ Λ = ς ≫ Λ')
    (u : C →ₗ[R] (A ⊗[R] C))
    (hu : ∀ c : C, u c = (CommRingCat.tensorProductIsoOfIsPushout hQ).inv.hom (ς.hom c)) :
    ∀ c : C,
      LinearMap.lTensor A u (u c) = LinearMap.lTensor A (TensorProduct.mk R A C 1) (u c) := by
  have pt := CommRingCat.isPushout_tensorProduct R A C
  have pt₃ := CommRingCat.isPushout_tensorProduct R A (A ⊗[R] C)
  have eΛ₁ : ∀ a : A, Λ.hom (kA.hom a) = i₃.hom a := fun a => ringHom_congr_apply hΛ₁ a
  have eΛ₂ : ∀ c : C, Λ.hom (kC.hom c) = j₃.hom (ς.hom c) := fun c => ringHom_congr_apply hΛ₂ c
  have eΛ₁' : ∀ a : A, Λ'.hom (kA.hom a) = i₃.hom a := fun a => ringHom_congr_apply hΛ₁' a
  have eΛ₂' : ∀ c : C, Λ'.hom (kC.hom c) = j₃.hom (kC.hom c) :=
    fun c => ringHom_congr_apply hΛ₂' c
  have ecoc : ∀ c : C, Λ.hom (ς.hom c) = Λ'.hom (ς.hom c) :=
    fun c => ringHom_congr_apply hcoc c
  have hA : ∀ a : A, (CommRingCat.tensorProductIsoOfIsPushout hQ).hom.hom
      (a ⊗ₜ[R] (1 : C)) = kA.hom a :=
    CommRingCat.tensorProductIsoOfIsPushout_hom_tmul_one hQ
  have hC : ∀ c : C, (CommRingCat.tensorProductIsoOfIsPushout hQ).hom.hom
      ((1 : A) ⊗ₜ[R] c) = kC.hom c :=
    CommRingCat.tensorProductIsoOfIsPushout_hom_one_tmul hQ
  have hinvA : ∀ a : A, (CommRingCat.tensorProductIsoOfIsPushout hQ).inv.hom (kA.hom a) =
      a ⊗ₜ[R] (1 : C) :=
    CommRingCat.tensorProductIsoOfIsPushout_inv_left hQ
  have hinvC : ∀ c : C, (CommRingCat.tensorProductIsoOfIsPushout hQ).inv.hom (kC.hom c) =
      (1 : A) ⊗ₜ[R] c :=
    CommRingCat.tensorProductIsoOfIsPushout_inv_right hQ
  set κ := CommRingCat.tensorProductIsoOfIsPushout hQ with hκ
  have hid : ∀ y : Q, κ.hom.hom (κ.inv.hom y) = y :=
    fun y => ringHom_congr_apply κ.inv_hom_id y
  -- the coaction as an `R`-algebra map
  obtain ⟨σ, hσ⟩ : ∃ σ : C →ₐ[R] (A ⊗[R] C), ∀ c : C, σ c = κ.inv.hom (ς.hom c) := by
    refine ⟨{ toRingHom := (ς ≫ κ.inv).hom, commutes' := fun r => ?_ }, fun _ => rfl⟩
    change κ.inv.hom (ς.hom (algebraMap R C r)) = _
    rw [IsScalarTower.algebraMap_apply R A C, hς, hinvA, Algebra.TensorProduct.algebraMap_apply]
  have hulin : u = σ.toLinearMap := LinearMap.ext fun c => by rw [hu]; exact (hσ c).symm
  -- the third pushout square, with its second leg the tensor product
  have hQ₃' : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R (A ⊗[R] C))) i₃ (κ.hom ≫ j₃) := by
    refine hQ₃.of_iso (Iso.refl _) (Iso.refl _) κ.symm (Iso.refl _) (by simp) ?_
      (by simp) (by simp)
    rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, Category.assoc]
    ext r
    change κ.inv.hom (kA.hom (algebraMap R A r)) = algebraMap R (A ⊗[R] C) r
    rw [hinvA, Algebra.TensorProduct.algebraMap_apply]
  have hi₃ : ∀ a : A, (CommRingCat.tensorProductIsoOfIsPushout hQ₃').inv.hom (i₃.hom a) =
      a ⊗ₜ[R] (1 : A ⊗[R] C) :=
    CommRingCat.tensorProductIsoOfIsPushout_inv_left hQ₃'
  have hj₃ : ∀ x : A ⊗[R] C, (CommRingCat.tensorProductIsoOfIsPushout hQ₃').inv.hom
      (j₃.hom (κ.hom.hom x)) = (1 : A) ⊗ₜ[R] x :=
    CommRingCat.tensorProductIsoOfIsPushout_inv_right hQ₃'
  set κ₃ := CommRingCat.tensorProductIsoOfIsPushout hQ₃' with hκ₃
  -- an `R`-algebra map `τ` induces the ring morphism `id ⊗ τ`, which `Λ₀` computes when it agrees
  -- with `i₃` on `kA` and with `j₃ ∘ τ` on `kC`
  have hmap : ∀ (Λ₀ : Q ⟶ Q₃) (τ : C →ₐ[R] (A ⊗[R] C)),
      (∀ a : A, Λ₀.hom (kA.hom a) = i₃.hom a) →
      (∀ c : C, Λ₀.hom (kC.hom c) = j₃.hom (κ.hom.hom (τ c))) → ∀ x : A ⊗[R] C,
      Algebra.TensorProduct.map (AlgHom.id R A) τ x = κ₃.inv.hom (Λ₀.hom (κ.hom.hom x)) := by
    intro Λ₀ τ h₁ h₂
    refine ringHom_congr_apply (g := CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R A) τ).toRingHom) (g' := κ.hom ≫ Λ₀ ≫ κ₃.inv)
      (pt.hom_ext ?_ ?_)
    · ext a
      change Algebra.TensorProduct.map (AlgHom.id R A) τ (a ⊗ₜ[R] (1 : C)) =
        κ₃.inv.hom (Λ₀.hom (κ.hom.hom (a ⊗ₜ[R] (1 : C))))
      rw [hA, h₁, hi₃, Algebra.TensorProduct.map_tmul, map_one]; rfl
    · ext c
      change Algebra.TensorProduct.map (AlgHom.id R A) τ ((1 : A) ⊗ₜ[R] c) =
        κ₃.inv.hom (Λ₀.hom (κ.hom.hom ((1 : A) ⊗ₜ[R] c)))
      rw [hC, h₂, Algebra.TensorProduct.map_tmul, map_one, hj₃]
  -- `lTensor` of an `R`-algebra map is `id ⊗ τ`
  have hlin : ∀ (τ : C →ₐ[R] (A ⊗[R] C)) (x : A ⊗[R] C),
      LinearMap.lTensor A τ.toLinearMap x = Algebra.TensorProduct.map (AlgHom.id R A) τ x := by
    intro τ x
    induction x with
    | add y z hy hz => rw [map_add, map_add, hy, hz]
    | tmul a c => rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul]; rfl
  have hmk : TensorProduct.mk R A C 1 =
      (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toLinearMap := rfl
  subst hulin
  intro c
  rw [hmk, hlin, hlin, hmap Λ σ eΛ₁ (fun c => by rw [eΛ₂, hσ, hid]), hmap Λ'
    Algebra.TensorProduct.includeRight eΛ₁' (fun c => by rw [eΛ₂']; exact congrArg _ (hC c).symm),
    hu c, hid, ecoc]

/-- **The hypothesis `hkey` of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK), discharged from the cocycle
diagram.**  In the situation of `ModuleCat.algebraTransitionOfPushout`, a third
pushout square presenting `Q₃` as `A ⊗[R] Q`, two morphisms `Λ, Λ' : Q ⟶ Q₃` pinned down on the
two legs of the second square, and the cocycle identity between their composites with the coaction
`iC ≫ Φ.hom`, give coassociativity of the unit of the transition isomorphism. -/
theorem unitCoassoc_algebraTransitionOfPushout
    (hP : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R A)) iC iA)
    (hQ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R C)) kA kC)
    (Φ : P ≅ Q)
    (h1 : CommRingCat.ofHom (algebraMap A C) ≫ iC ≫ Φ.hom = kA)
    (h2 : iA ≫ Φ.hom = CommRingCat.ofHom (algebraMap A C) ≫ kC)
    (hQ₃ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R A) ≫ kA) i₃ j₃)
    {Λ Λ' : Q ⟶ Q₃}
    (hΛ₁ : kA ≫ Λ = i₃) (hΛ₂ : kC ≫ Λ = (iC ≫ Φ.hom) ≫ j₃)
    (hΛ₁' : kA ≫ Λ' = i₃) (hΛ₂' : kC ≫ Λ' = kC ≫ j₃)
    (hcoc : (iC ≫ Φ.hom) ≫ Λ = (iC ≫ Φ.hom) ≫ Λ') :
    ∀ c : C,
      LinearMap.lTensor A (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2))
          (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2) c) =
        LinearMap.lTensor A (TensorProduct.mk R A C 1)
          (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2) c) :=
  unitCoassoc_of_cocycle hQ hQ₃ (iC ≫ Φ.hom) (fun a => ringHom_congr_apply h1 a)
    hΛ₁ hΛ₂ hΛ₁' hΛ₂' hcoc _
    (algebraUnitTransition_algebraTransitionOfPushout hP hQ Φ h1 h2)

/-- **Step 4 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) from the
cocycle diagram.**  For `R → A` faithfully flat, the two instances of Stacks 0APJ and the cocycle
diagram of `ModuleCat.unitCoassoc_algebraTransitionOfPushout` make `C` the base
change to `A` of the `R`-subalgebra of `ψ`-invariants.

This is `ModuleCat.isPushout_descentInvariants_of_isPushout` with its
coassociativity hypothesis discharged. -/
theorem isPushout_descentInvariants_of_cocycleDiagram [Module.FaithfullyFlat R A]
    (hP : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R A)) iC iA)
    (hQ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R C)) kA kC)
    (Φ : P ≅ Q)
    (h1 : CommRingCat.ofHom (algebraMap A C) ≫ iC ≫ Φ.hom = kA)
    (h2 : iA ≫ Φ.hom = CommRingCat.ofHom (algebraMap A C) ≫ kC)
    (hQ₃ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R A) ≫ kA) i₃ j₃)
    {Λ Λ' : Q ⟶ Q₃}
    (hΛ₁ : kA ≫ Λ = i₃) (hΛ₂ : kC ≫ Λ = (iC ≫ Φ.hom) ≫ j₃)
    (hΛ₁' : kA ≫ Λ' = i₃) (hΛ₂' : kC ≫ Λ' = kC ≫ j₃)
    (hcoc : (iC ≫ Φ.hom) ≫ Λ = (iC ≫ Φ.hom) ≫ Λ') :
    Algebra.IsPushout R A
      (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C :=
  isPushout_descentInvariants_of_isPushout hP hQ Φ h1 h2
    (unitCoassoc_algebraTransitionOfPushout hP hQ Φ h1 h2 hQ₃ hΛ₁ hΛ₂ hΛ₁' hΛ₂' hcoc)

/-- **The hypotheses of `ModuleCat.unitCoassoc_of_cocycle` are jointly satisfiable.**  For `C = A`
and the canonical presentations of `A ⊗[R] A` and of `A ⊗[R] (A ⊗[R] A)` as pushouts, the whole
cocycle diagram exists: the coaction `a ↦ a ⊗ 1`, the morphism `Λ` sending `a ⊗ b` to
`a ⊗ (b ⊗ 1)` and the morphism `Λ'` sending `a ⊗ b` to `a ⊗ (1 ⊗ b)` satisfy all five equations.

This is the trivial descent datum, and the point of recording it is that no automatic check
detects a theorem made vacuous by unsatisfiable hypotheses: the cocycle diagram of
`ModuleCat.unitCoassoc_of_cocycle`, of
`ModuleCat.unitCoassoc_algebraTransitionOfPushout` and of
`AlgebraicGeometry.DescentDatum.unitCoassoc_descentAlgebraTransition` is a condition some data
really does satisfy. -/
theorem exists_cocycleDiagram_of_algebra (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    ∃ (Q Q₃ : CommRingCat.{u}) (kA kC : CommRingCat.of A ⟶ Q)
      (i₃ : CommRingCat.of A ⟶ Q₃) (j₃ Λ Λ' : Q ⟶ Q₃) (ς : CommRingCat.of A ⟶ Q)
      (_hQ : IsPushout (CommRingCat.ofHom (algebraMap R A))
        (CommRingCat.ofHom (algebraMap R A)) kA kC),
      IsPushout (CommRingCat.ofHom (algebraMap R A))
          (CommRingCat.ofHom (algebraMap R A) ≫ kA) i₃ j₃ ∧
        (∀ a : A, ς.hom (algebraMap A A a) = kA.hom a) ∧
        kA ≫ Λ = i₃ ∧ kC ≫ Λ = ς ≫ j₃ ∧ kA ≫ Λ' = i₃ ∧ kC ≫ Λ' = kC ≫ j₃ ∧
        ς ≫ Λ = ς ≫ Λ' := by
  refine ⟨CommRingCat.of (A ⊗[R] A), CommRingCat.of (A ⊗[R] (A ⊗[R] A)),
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := A)),
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A)).toRingHom,
    CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := A ⊗[R] A)),
    CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A ⊗[R] A)).toRingHom,
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R A)
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A)).toRingHom,
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R A)
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A)).toRingHom,
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := A)),
    CommRingCat.isPushout_tensorProduct R A A, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (CommRingCat.ofHom (algebraMap R A) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := A)) :
          CommRingCat.of R ⟶ CommRingCat.of (A ⊗[R] A))
        = CommRingCat.ofHom (algebraMap R (A ⊗[R] A)) := by
      ext r
      change (algebraMap R A r) ⊗ₜ[R] (1 : A) = algebraMap R (A ⊗[R] A) r
      rw [Algebra.TensorProduct.algebraMap_apply]
    rw [h]
    exact CommRingCat.isPushout_tensorProduct R A (A ⊗[R] A)
  · intro a
    change a ⊗ₜ[R] (1 : A) = a ⊗ₜ[R] (1 : A)
    rfl
  all_goals
    ext a
    simp

end ModuleCat

namespace AlgebraicGeometry.DescentDatum

section StepFour

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (E : Set D.over.left)
    [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    (hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E)
    (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      D.over.hom.appTop ≫ D.over.left.topToSubset E)
    [IsAffine S] [IsAffine X] [Flat f] [QuasiSeparatedSpace D.over.left]
    {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
    (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E))

omit [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
  [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
  [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)] in
include hRA hU hE in
/-- **The third instance of Stacks 0APJ needed by step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK).**  For `f : X ⟶ S` flat between
affine schemes and `E` an intersection of a nonempty family of quasi-compact opens of the
quasi-separated `V`,
```
Γ(X ×_S (X ×_S E), 𝒪) = Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(X ×_S E, 𝒪),
```
as a pushout square of rings.  This is the square `hQ₃` of
`ModuleCat.unitCoassoc_algebraTransitionOfPushout` and of
`AlgebraicGeometry.DescentDatum.unitCoassoc_descentAlgebraTransition`, so the only parts of the
cocycle diagram still owed after it are the two morphisms `Λ`, `Λ'` and the cocycle identity.

It is `AlgebraicGeometry.isPushout_sectionsRingOnSubsetMap_of_flat_of_isAffine` applied to the
Cartesian square presenting `(X ×_S V) ×_S X` over the structure morphism of `X ×_S V`, flipped so
that the `Γ(X, ⊤)`-leg comes first; `X ×_S V` is quasi-separated because `f` is a morphism of
affine schemes, hence quasi-separated, and `X ×_S E` is the intersection of the preimages of the
`U i`, each quasi-compact because `f` is quasi-compact. -/
theorem isPushout_algebraMap_transitionTargetBaseChange :
    IsPushout (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) ≫
        (pullback.fst f (D.over.hom ≫ f)).appTop ≫
          (pullback f (D.over.hom ≫ f)).topToSubset
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
      ((pullback.snd (pullback.fst f (D.over.hom ≫ f) ≫ f) f).appTop ≫
        (pullback (pullback.fst f (D.over.hom ≫ f) ≫ f) f).topToSubset
          (⇑(pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f) ⁻¹'
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)))
      (Scheme.sectionsRingOnSubsetMap (pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f)
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)
        (⇑(pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f) ⁻¹'
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) (Set.Subset.refl _)) := by
  have _hqs : QuasiSeparatedSpace ((pullback f (D.over.hom ≫ f) : Scheme.{u}) : Type u) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (D.over.hom ≫ f))
  have hπ : IsPullback (pullback.fst (pullback.fst f (D.over.hom ≫ f) ≫ f) f)
      (pullback.snd (pullback.fst f (D.over.hom ≫ f) ≫ f) f)
      (pullback.fst f (D.over.hom ≫ f) ≫ f) f := IsPullback.of_hasPullback _ _
  obtain ⟨U', hU'eq⟩ : ∃ U' : I → (pullback f (D.over.hom ≫ f)).Opens,
      ∀ i, U' i = (pullback.snd f (D.over.hom ≫ f)) ⁻¹ᵁ (U i) :=
    ⟨fun i => (pullback.snd f (D.over.hom ≫ f)) ⁻¹ᵁ (U i), fun _ => rfl⟩
  have hU'c : ∀ i, IsCompact (U' i : Set ↥(pullback f (D.over.hom ≫ f) : Scheme.{u})) := fun i => by
    rw [hU'eq]
    exact QuasiCompact.isCompact_preimage (f := pullback.snd f (D.over.hom ≫ f)) _
      (U i).isOpen (hU i)
  have hE' : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) =
      ⋂ i, (U' i : Set ↥(pullback f (D.over.hom ≫ f) : Scheme.{u})) := by
    rw [hE, Set.preimage_iInter]
    exact Set.iInter_congr fun i => by rw [hU'eq]; rfl
  have hpush := (isPushout_sectionsRingOnSubsetMap_of_flat_of_isAffine hπ _ hU'c
    (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) hE').flip
  rw [hRA]
  have hcomp : (pullback.fst f (D.over.hom ≫ f) ≫ f).appTop ≫
      (pullback f (D.over.hom ≫ f)).topToSubset (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)
      = f.appTop ≫ (pullback.fst f (D.over.hom ≫ f)).appTop ≫
        (pullback f (D.over.hom ≫ f)).topToSubset
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) := by
    rw [Scheme.Hom.comp_appTop, Category.assoc]
  rw [← hcomp]
  exact hpush

include hRA hRC hAC in
/-- **The coassociativity obligation of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) for a descent datum, from the
cocycle diagram.**  Let `f : X ⟶ S` be a flat morphism of affine schemes, let `D` be a descent
datum relative to `f` whose scheme `V` is quasi-separated, and let `E ⊆ V` be an intersection of a
nonempty family of quasi-compact opens whose two preimages are exchanged by the gluing
isomorphism.  Write `Q = Γ(X ×_S E, 𝒪)` for the apex of the second instance of Stacks 0APJ.  Given

* a pushout square presenting a ring `Q₃` as `Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Q` — geometrically
  `Q₃ = Γ(X ×_S (X ×_S E), 𝒪)`;
* two morphisms `Λ, Λ' : Q ⟶ Q₃`, the first restricting to the `Γ(X, ⊤)`-leg of `Q₃` on the
  `Γ(X, ⊤)`-leg of `Q` and to the coaction followed by the `Q`-leg on the `Γ(E, 𝒪_V|_E)`-leg, the
  second restricting to the `Γ(X, ⊤)`-leg and to the `Q`-leg respectively;
* the cocycle identity `ς ≫ Λ = ς ≫ Λ'` for the coaction `ς`,

the unit of `AlgebraicGeometry.DescentDatum.descentAlgebraTransition` is coassociative.  That is
the hypothesis `hkey` of
`AlgebraicGeometry.DescentDatum.isPushout_descentInvariants_of_cocycle` and of
`AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_legs_of_restrictOpen`.

Geometrically `Λ` is restriction along `(x₁, v, x₂) ↦ (x₂, x₁ · v)` and `Λ'` along
`(x₁, v, x₂) ↦ (x₂, v)`, so the cocycle identity is `x₂ · (x₁ · v) = x₂ · v`.  This is
`ModuleCat.unitCoassoc_algebraTransitionOfPushout` fed by the two instances of Stacks 0APJ and the
two compatibilities of `Φ` with `Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(X, ⊤)`. -/
theorem unitCoassoc_descentAlgebraTransition
    {Q₃ : CommRingCat.{u}} {i₃ : CommRingCat.of ↥Γ(X, ⊤) ⟶ Q₃}
    {j₃ : (pullback f (D.over.hom ≫ f)).sectionsRingOnSubset
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⟶ Q₃}
    (hQ₃ : IsPushout (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) ≫
        (pullback.fst f (D.over.hom ≫ f)).appTop ≫
          (pullback f (D.over.hom ≫ f)).topToSubset
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) i₃ j₃)
    {Λ Λ' : (pullback f (D.over.hom ≫ f)).sectionsRingOnSubset
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⟶ Q₃}
    (hΛ₁ : ((pullback.fst f (D.over.hom ≫ f)).appTop ≫
        (pullback f (D.over.hom ≫ f)).topToSubset
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) ≫ Λ = i₃)
    (hΛ₂ : Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) ≫ Λ =
      (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
          (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
        (D.transitionSectionsIso E h₁ h₂).hom) ≫ j₃)
    (hΛ₁' : ((pullback.fst f (D.over.hom ≫ f)).appTop ≫
        (pullback f (D.over.hom ≫ f)).topToSubset
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) ≫ Λ' = i₃)
    (hΛ₂' : Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) ≫ Λ' =
      Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) ≫ j₃)
    (hcoc : (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
          (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
        (D.transitionSectionsIso E h₁ h₂).hom) ≫ Λ =
      (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
          (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
        (D.transitionSectionsIso E h₁ h₂).hom) ≫ Λ') :
    ∀ c : ↥(D.over.left.sectionsRingOnSubset E),
      LinearMap.lTensor ↥Γ(X, ⊤)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂) c) =
        LinearMap.lTensor ↥Γ(X, ⊤)
          (TensorProduct.mk ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E) 1)
          (ModuleCat.algebraUnitTransition ↥Γ(S, ⊤) ↥Γ(X, ⊤) _
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂) c) :=
  ModuleCat.unitCoassoc_algebraTransitionOfPushout
    (D.isPushout_algebraMap_transitionSource E hRA hRC U hU hE)
    (D.isPushout_algebraMap_transitionTarget E hRA hRC U hU hE)
    (D.transitionSectionsIso E h₁ h₂)
    (D.algebraMap_comp_transitionSectionsIso_hom E hAC h₁ h₂)
    (D.transitionSectionsIso_hom_eq_algebraMap_comp E hAC h₁ h₂)
    hQ₃ hΛ₁ hΛ₂ hΛ₁' hΛ₂' hcoc

end StepFour

section Residue

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- **The residue of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) over an affine
base, with the coassociativity obligation replaced by a cocycle diagram.**  Let `f : X ⟶ S` be a
surjective flat quasi-compact morphism of affine schemes and let `D` be a descent datum relative
to `f` whose scheme over `X` is ind-quasi-affine.  Then `D` is effective as soon as

1. `hcocycle`: for every intersection `E` of a nonempty family of quasi-compact opens whose two
   preimages are exchanged by the gluing isomorphism, the ring of functions on `X ×_S E` carries
   the cocycle diagram of
   `AlgebraicGeometry.DescentDatum.unitCoassoc_descentAlgebraTransition` — a pushout square
   presenting a ring `Q₃` as `Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(X ×_S E, 𝒪)`, two morphisms `Λ, Λ'` out of
   `Γ(X ×_S E, 𝒪)` pinned down on the two legs of that square, and the cocycle identity between
   their composites with the coaction.  **This replaces the `hkey` of
   `AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_legs_of_restrictOpen`**, which is
   an identity in `Γ(X, ⊤) ⊗ (Γ(X, ⊤) ⊗ Γ(E, 𝒪_V|_E))` that no geometric statement bears on; the
   diagram asked for here is the one the source's own step 4 produces, and its three parts are
   Stacks 0APJ for `X ×_S (X ×_S E) ⊆ X ×_S (X ×_S V)`, restriction along the two maps
   `(x₁, v, x₂) ↦ (x₂, x₁ · v)` and `(x₁, v, x₂) ↦ (x₂, v)`, and the cocycle condition
   `x₂ · (x₁ · v) = x₂ · v` of the datum;
2. `hlegs`, `hrestrict` and `hglueing`: unchanged, character for character, from
   `AlgebraicGeometry.DescentDatum.isEffective_of_unitCoassoc_of_legs_of_restrictOpen`.

The pushout square inside `hcocycle` is proved, as
`AlgebraicGeometry.DescentDatum.isPushout_algebraMap_transitionTargetBaseChange`, so a supplier of
`hcocycle` discharges it by
`⟨_, _, _, Λ, Λ', D.isPushout_algebraMap_transitionTargetBaseChange E hRA U hU hE, …⟩` and owes
only `Λ`, `Λ'` and their five equations.

**This is not Stacks 0APK and carries no tag.**  It is a reduction: a statement with four
hypotheses which no declaration of this repository discharges. -/
theorem isEffective_of_cocycleDiagram_of_legs_of_restrictOpen
    [IsAffine S] [IsAffine X] [Flat f] [Surjective f] [QuasiCompact f]
    [IsIndQuasiAffineHom D.over.hom]
    (hcocycle : ∀ (E : Set D.over.left)
      [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      (_hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
      (_hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E)
      (_hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        D.over.hom.appTop ≫ D.over.left.topToSubset E)
      [QuasiSeparatedSpace D.over.left] {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (_hU : ∀ i, IsCompact (U i : Set D.over.left))
      (_hE : E = ⋂ i, (U i : Set D.over.left))
      (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
      (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)),
      ∃ (Q₃ : CommRingCat.{u}) (i₃ : CommRingCat.of ↥Γ(X, ⊤) ⟶ Q₃)
        (j₃ Λ Λ' : (pullback f (D.over.hom ≫ f)).sectionsRingOnSubset
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⟶ Q₃),
        IsPushout (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)))
            (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) ≫
              (pullback.fst f (D.over.hom ≫ f)).appTop ≫
                (pullback f (D.over.hom ≫ f)).topToSubset
                  (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) i₃ j₃ ∧
          ((pullback.fst f (D.over.hom ≫ f)).appTop ≫
            (pullback f (D.over.hom ≫ f)).topToSubset
              (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) ≫ Λ = i₃ ∧
          Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
              (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) ≫ Λ =
            (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
                (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
              (D.transitionSectionsIso E h₁ h₂).hom) ≫ j₃ ∧
          ((pullback.fst f (D.over.hom ≫ f)).appTop ≫
            (pullback f (D.over.hom ≫ f)).topToSubset
              (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E)) ≫ Λ' = i₃ ∧
          Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
              (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) ≫ Λ' =
            Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
              (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) ≫ j₃ ∧
          (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
                (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
              (D.transitionSectionsIso E h₁ h₂).hom) ≫ Λ =
            (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
                (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
              (D.transitionSectionsIso E h₁ h₂).hom) ≫ Λ')
    (hlegs : ∀ (E : Set D.over.left) {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (_hU : ∀ i, IsCompact (U i : Set D.over.left))
      (_hE : E = ⋂ i, (U i : Set D.over.left)) (hEinv : D.IsTransitionInvariantSet E)
      (W : D.over.left.Opens) (_hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E),
      (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
            (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
          (D.transitionSectionsIso E
            (D.subset_preimage_transitionPullbackIso_hom_of_invariantSet E hEinv)
            (D.subset_preimage_transitionPullbackIso_inv_of_invariantSet E hEinv)).hom)).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left) =
        (Spec.map (Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
            (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _))).base ⁻¹'
          subsetΓSpecImage D.over.left E (W : Set D.over.left))
    (hrestrict : ∀ (E : Set D.over.left)
      [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
      (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
      (hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E)
      (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
        D.over.hom.appTop ≫ D.over.left.topToSubset E)
      [QuasiSeparatedSpace D.over.left] {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
      (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
      (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
      (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
        ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E))
      (W : D.over.left.Opens) (hWinv : D.IsTransitionInvariant W)
      (_hWE : (W : Set D.over.left) ⊆ E)
      (W₀ : (Spec (CommRingCat.of ↥(ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
          ↥(D.over.left.sectionsRingOnSubset E)
          (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂)))).Opens)
      (_hW₀ : ((Spec.map (CommRingCat.ofHom (algebraMap
            (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
              ↥(D.over.left.sectionsRingOnSubset E)
              (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
            ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
            (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
          Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) =
        subsetΓSpecImage D.over.left E (W : Set D.over.left)),
      DescentData.IsEffective (D.restrictOpen W hWinv))
    (hglueing : (∀ v : D.over.left, ∃ (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W),
        v ∈ W ∧ DescentData.IsEffective (D.restrictOpen W hW)) →
      DescentData.IsEffective D) :
    DescentData.IsEffective D := by
  refine D.isEffective_of_unitCoassoc_of_legs_of_restrictOpen ?_ hlegs hrestrict hglueing
  intro E _ _ _ _ hRA hRC hAC _ I _ U hU hE h₁ h₂ c
  obtain ⟨Q₃, i₃, j₃, Λ, Λ', hQ₃, hΛ₁, hΛ₂, hΛ₁', hΛ₂', hcoc⟩ :=
    hcocycle E hRA hRC hAC U hU hE h₁ h₂
  exact D.unitCoassoc_descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂
    hQ₃ hΛ₁ hΛ₂ hΛ₁' hΛ₂' hcoc c

end Residue

end AlgebraicGeometry.DescentDatum

end

end
