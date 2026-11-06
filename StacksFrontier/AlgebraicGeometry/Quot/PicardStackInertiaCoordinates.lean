module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackInertia
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackInertiaProduct

/-!
# The inertia stack of the Picard stack is `𝐆_{m, S} ×_S Picardstack_{X/B}`

Stacks 0375: under the hypothesis that the structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an
isomorphism for every test scheme `T`, the inertia stack of
`Picardstack_{X/B}` is equivalent, as a category over `(Sch/S)_fppf`, to the product of the
category of elements of `𝐆_{m, S}` with `Picardstack_{X/B}`.

## Main definitions

* `AlgebraicGeometry.Space.PicardObject.unitsSMulAut`: the automorphism of the invertible module
  of an object over `T` given by multiplication by an invertible regular function on `T`.
* `AlgebraicGeometry.Space.PicardObject.autEquivMultiplicativeGroupPoints`: under that
  hypothesis, every automorphism of the invertible module is of that form for exactly one
  invertible function, so the automorphism group is `𝐆_{m, S}(T)`.
* `AlgebraicGeometry.Space.PicardCategoryData.multiplicativeGroupCoordinates`: these coordinates,
  for all objects at once, are compatible with the morphisms of `Picardstack_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.structureUnitsIso_of_structureSheafMapIso`: under
  that hypothesis, the invertible global functions of `X_T` are the invertible regular functions
  on `T`.
* `AlgebraicGeometry.Space.nonempty_autLineBundle_mulEquiv_multiplicativeGroupPoints_of_iso` and
  `AlgebraicGeometry.Space.nonempty_vertical_equiv_multiplicativeGroupPoints_of_iso`: the
  automorphisms of the invertible module of an object over `T`, and the points of the inertia
  stack above it, are `𝐆_{m, S}(T)`.
* `AlgebraicGeometry.Space.PicardCategoryData.multiplicativeGroupCoordinatesIso`: these
  coordinates are compatible with the composition of `Picardstack_{X/B}`.
* In `AlgebraicGeometry.Space`,
  `nonempty_equivalenceOver_picardInertia_multiplicativeGroupProduct_of_iso`:
  `I_{Picardstack_{X/B}} = 𝐆_{m, S} ×_S Picardstack_{X/B}` as categories over the big fppf site.

## Implementation notes

Stacks 0375 identifies an automorphism `α` of the line bundle `L` on `X_T` with an
element of `H^0(X_T, 𝒪_{X_T})^* = H^0(T, 𝒪_T^*)`.  Here that identification is made explicit:
the regular function `u` on `T` is pulled back to `X_T`
(`AlgebraicGeometry.Space.baseChangeGlobalFunctions`), and `α` is multiplication by it
(`AlgebraicGeometry.Space.globalFunctionSMul`).  Being explicit is what makes the compatibility
with the morphisms of `Picardstack_{X/B}` provable: a morphism `(g, φ)` commutes with two vertical
automorphisms iff `φ ∘ g^*(u_C ·) = (u_A ·) ∘ φ`
(`AlgebraicGeometry.Space.PicardHom.comp_verticalOfAut_eq_iff`); inverse image along the morphism
of base changes carries multiplication by `u_C` to multiplication by its pullback
(`AlgebraicGeometry.Space.modulePullback_map_globalFunctionSMul`); a comparison of modules
commutes with multiplication by global functions; and on an invertible module multiplication by
a global function determines the function.  So the commutation is `g^*u_C = u_A`, which is the
restriction of points of `𝐆_{m, S}`.

## References

* [Stacks Project, Tag 0375](https://stacks.math.columbia.edu/tag/0375)
* [Stacks Project, Tag 0DNH](https://stacks.math.columbia.edu/tag/0DNH)
* [Stacks Project, Tag 022U](https://stacks.math.columbia.edu/tag/022U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {s : PicardSituation B S hS}

/-! ### The vertical automorphisms of the Picard stack in coordinates -/

/-- The vertical endomorphism of an object of `Picardstack_{X/B}` attached to an automorphism of
its invertible module: the identity of the object, with its comparison of modules followed by the
automorphism.  It is the inverse of `AlgebraicGeometry.Space.verticalEquivAut`. -/
def PicardObject.verticalOfAut (A : PicardObject s) (α : A.lineBundle ≅ A.lineBundle) :
    PicardHom A A where
  base := (PicardHom.id (modulePushforwardCoherence B S hS) A).base
  fibre := (PicardHom.id (modulePushforwardCoherence B S hS) A).fibre ≫ α.hom
  isIso_fibre := inferInstance

/-- A vertical endomorphism is the one attached to its automorphism of the invertible module. -/
theorem PicardObject.Vertical.eq_verticalOfAut {A : PicardObject s} (v : A.Vertical) :
    v.1 = A.verticalOfAut (verticalEquivAut (modulePushforwardCoherence B S hS) A v) := by
  obtain ⟨⟨b, φ, hφ⟩, hb⟩ := v
  change b = 𝟙 A.T at hb
  subst hb
  refine PicardHom.ext rfl ?_
  refine (eqToHom_refl_comp_picard _ _).trans ?_
  show φ = (PicardObject.unitComparison (modulePushforwardCoherence B S hS) A).hom ≫
    (PicardObject.unitComparison (modulePushforwardCoherence B S hS) A).inv ≫
      ((baseChangeMapComparison s.f (rfl : 𝟙 A.T = 𝟙 A.T)).app A.lineBundle).inv ≫ φ
  rw [Iso.hom_inv_id_assoc]
  simp [baseChangeMapComparison]

/-- The morphism of `Picardstack_{X/B}` with the same base map as `m` and with comparison of
modules `φ` changed to `ψ`. -/
def PicardHom.withFibre {A C : PicardObject s} (m : PicardHom A C)
    (ψ : (modulePullback B S hS (baseChangeMap s.f m.base)).obj C.lineBundle ⟶ A.lineBundle)
    [IsIso ψ] : PicardHom A C where
  base := m.base
  fibre := ψ
  isIso_fibre := inferInstance

/-- Changing the last factor of a composite of comparisons of modules by an endomorphism is
changing the middle factor by its image. -/
theorem Functor.fibreComp_comp_right {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀}
    (τ : Lab ≅ Lb ⋙ La) {M : C₀} {M' : C₁} {M'' : C₂} (a : La.obj M' ⟶ M)
    (b : Lb.obj M'' ⟶ M') (c : M' ⟶ M') :
    Functor.fibreComp τ a (b ≫ c) = Functor.fibreComp τ (La.map c ≫ a) b :=
  Functor.fibreComp_comp_map τ a b c

/-- The comparison of modules of a morphism followed by a vertical endomorphism of its target is
the inverse image of the automorphism followed by the comparison of the morphism. -/
theorem PicardHom.comp_verticalOfAut_fibre {A C : PicardObject s} (m : PicardHom A C)
    (β : C.lineBundle ≅ C.lineBundle) :
    (PicardHom.comp m (C.verticalOfAut β)).fibre =
      (baseChangeMapComparison s.f (Category.comp_id m.base)).hom.app C.lineBundle ≫
        (modulePullback B S hS (baseChangeMap s.f m.base)).map β.hom ≫ m.fibre := by
  have h1 := (PicardHom.comp_fibre (m.withFibre
      ((modulePullback B S hS (baseChangeMap s.f m.base)).map β.hom ≫ m.fibre))
    (PicardHom.id (modulePushforwardCoherence B S hS) C)).symm.trans
    (PicardHom.comp_id_right_fibre (modulePushforwardCoherence B S hS) (m.withFibre
      ((modulePullback B S hS (baseChangeMap s.f m.base)).map β.hom ≫ m.fibre)))
  dsimp only [PicardHom.withFibre] at h1
  rw [PicardHom.comp_fibre]
  dsimp only [PicardObject.verticalOfAut]
  rw [Functor.fibreComp_comp_right]
  exact h1

/-- Moving an endomorphism past a transformation into the identity functor in a composite of
comparisons of modules. -/
theorem Functor.fibreComp_natTrans_comp {C₀ : Type*} {C₂ : Type*} [Category* C₀] [Category* C₂]
    {La : C₀ ⥤ C₀} {Lb : C₂ ⥤ C₀} {Lab : C₂ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La) (η : La ⟶ 𝟭 C₀)
    {M : C₀} {M'' : C₂} (c : M ⟶ M) (b : Lb.obj M'' ⟶ M) :
    Functor.fibreComp τ (η.app M ≫ c) b = Functor.fibreComp τ (η.app M) (b ≫ c) :=
  Functor.fibreComp_natTrans_app_comp τ η c b

/-- The comparison of modules of a vertical endomorphism of its source followed by a morphism is
the comparison of the morphism followed by the automorphism. -/
theorem PicardHom.verticalOfAut_comp_fibre {A C : PicardObject s} (m : PicardHom A C)
    (α : A.lineBundle ≅ A.lineBundle) :
    (PicardHom.comp (A.verticalOfAut α) m).fibre =
      (baseChangeMapComparison s.f (Category.id_comp m.base)).hom.app C.lineBundle ≫
        m.fibre ≫ α.hom := by
  have h1 := (PicardHom.comp_fibre (PicardHom.id (modulePushforwardCoherence B S hS) A)
    (m.withFibre (m.fibre ≫ α.hom))).symm.trans
    (PicardHom.comp_id_left_fibre (modulePushforwardCoherence B S hS)
      (m.withFibre (m.fibre ≫ α.hom)))
  dsimp only [PicardHom.withFibre, PicardHom.id] at h1
  rw [PicardHom.comp_fibre]
  dsimp only [PicardObject.verticalOfAut, PicardHom.id]
  rw [Functor.fibreComp_natTrans_comp]
  exact h1

/-- Two morphisms of `Picardstack_{X/B}` with base maps equal to `g` and comparisons of modules
which, read through those equalities, are `X` and `Y`, are equal exactly when `X = Y`. -/
theorem PicardHom.eq_iff_of_fibre_eq {A C : PicardObject s} {m n : PicardHom A C}
    {g : A.T ⟶ C.T} (hm : m.base = g) (hn : n.base = g)
    (X Y : (modulePullback B S hS (baseChangeMap s.f g)).obj C.lineBundle ⟶ A.lineBundle)
    (hmX : m.fibre = eqToHom (by rw [hm]) ≫ X) (hnY : n.fibre = eqToHom (by rw [hn]) ≫ Y) :
    m = n ↔ X = Y := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = g at hm
  change nb = g at hn
  subst hm hn
  change mf = eqToHom rfl ≫ X at hmX
  change nf = eqToHom rfl ≫ Y at hnY
  rw [eqToHom_refl, Category.id_comp] at hmX hnY
  subst hmX hnY
  exact ⟨fun h => eq_of_heq (PicardHom.mk.inj h).2, fun h => by subst h; rfl⟩

/-- **A morphism of `Picardstack_{X/B}` commutes with two vertical endomorphisms exactly when its
comparison of modules intertwines the two automorphisms of the invertible modules.**  For
`m = (g, φ)` from `A` to `C`, and vertical endomorphisms with automorphisms `α` of `L_A` and `β`
of `L_C`, the two composites `m ∘ β` and `α ∘ m` agree iff `φ ∘ g^*β = α ∘ φ`. -/
theorem PicardHom.comp_verticalOfAut_eq_iff {A C : PicardObject s} (m : PicardHom A C)
    (α : A.lineBundle ≅ A.lineBundle) (β : C.lineBundle ≅ C.lineBundle) :
    PicardHom.comp m (C.verticalOfAut β) = PicardHom.comp (A.verticalOfAut α) m ↔
      (modulePullback B S hS (baseChangeMap s.f m.base)).map β.hom ≫ m.fibre =
        m.fibre ≫ α.hom :=
  PicardHom.eq_iff_of_fibre_eq (m := PicardHom.comp m (C.verticalOfAut β))
    (n := PicardHom.comp (A.verticalOfAut α) m)
    (Category.comp_id m.base) (Category.id_comp m.base)
    ((modulePullback B S hS (baseChangeMap s.f m.base)).map β.hom ≫ m.fibre) (m.fibre ≫ α.hom)
    ((PicardHom.comp_verticalOfAut_fibre m β).trans
      (by simp only [baseChangeMapComparison, eqToIso.hom, eqToHom_app]; rfl))
    ((PicardHom.verticalOfAut_comp_fibre m α).trans
      (by simp only [baseChangeMapComparison, eqToIso.hom, eqToHom_app]; rfl))

/-! ### Automorphisms of the invertible modules as invertible functions on the test scheme -/

/-- The global functions of `X_T` attached to an invertible regular function on `T` and to its
inverse multiply to `1`. -/
theorem baseChangeGlobalFunctions_val_mul {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : SchemesOver Y) (a b : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T.left)))
    (U : (SmallEtale B S hS (baseChangeSpace f T).1)ᵒᵖ) :
    (baseChangeGlobalFunctions f T (a * b)).val U =
      (baseChangeGlobalFunctions f T a).val U * (baseChangeGlobalFunctions f T b).val U := by
  rw [map_mul]
  rfl

/-- The global function of `X_T` attached to the regular function `1` on `T` is `1`. -/
theorem baseChangeGlobalFunctions_val_one {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : SchemesOver Y) (U : (SmallEtale B S hS (baseChangeSpace f T).1)ᵒᵖ) :
    (baseChangeGlobalFunctions f T 1).val U = 1 := by
  rw [map_one]
  rfl

/-- **Under the hypothesis of Stacks 0375 the global functions of `X_T` are the regular functions
on `T`.**  Pullback along the projection `X_T ⟶ T` is a bijection. -/
theorem bijective_baseChangeGlobalFunctions (h : s.StructureSheafMapIso) (T : s.SchemesOver) :
    Function.Bijective (fun a ↦ (baseChangeGlobalFunctions s.f T a :
      globalFunctions B S hS (s.baseChange T).1)) := by
  simp only [baseChangeGlobalFunctions_eq_terminalChartPullback]
  exact bijective_terminalChartPullback B S hS (baseChangeInclusion s.f T)
    (idEtaleChart B S hS T.left)
    (by show IsIso (𝟙 ((schemeSpaceFunctor B S hS).obj T.left)); infer_instance) (h T)

/-- Under the hypothesis of Stacks 0375, the automorphism group of the structure module of the
base change `X_T` — its group of invertible global functions, `H^0(X_T, 𝒪_{X_T})^*` — is the group
`H^0(T, 𝒪_T)^*` of invertible regular functions on `T`. -/
theorem PicardSituation.structureUnitsIso_of_structureSheafMapIso (s : PicardSituation B S hS) :
    s.StructureUnitsIso := fun h T ↦
  ⟨((Aut.unitsEndEquivAut (structureModule (s.baseChange T))).symm.trans
      (Units.mapEquiv (unitEndRingEquivGlobalFunctions B S hS
        (s.baseChange T).1 (s.baseChange T).2).toMulEquiv)).trans
    (Units.mapEquiv (RingEquiv.ofBijective (baseChangeGlobalFunctions s.f T)
      (bijective_baseChangeGlobalFunctions h T)).toMulEquiv).symm⟩

/-- **The `𝐆_m` factor of the inertia stack.**  Assume that for every test scheme `T`
over the base the structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the base change is an isomorphism.
Then for every object `(U, b, L)` of `Picardstack_{X/B}` the automorphism group of `L` is the
group `𝐆_{m, S}(U)`. -/
@[stacks 0375 "the 𝐆_m factor of the inertia stack: under the hypothesis that 𝒪_T ⟶ f_{T,*}𝒪_{X_T} \
is an isomorphism for every test scheme T, the automorphism group of the invertible module of an \
object of the Picard stack over T is 𝐆_{m,S}(T)"]
theorem nonempty_autLineBundle_mulEquiv_multiplicativeGroupPoints_of_iso
    (h : s.StructureSheafMapIso) (A : PicardObject s) :
    Nonempty (Aut A.lineBundle ≃* multiplicativeGroupPointsAt B S hS A.T.left) :=
  nonempty_autLineBundle_mulEquiv_multiplicativeGroupPoints h
    (s.structureUnitsIso_of_structureSheafMapIso) A

/-- **The points of the inertia stack.**  Assume that for every test scheme `T` over the base the
structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the base change is an isomorphism.  Then the
endomorphisms of an object `(U, b, L)` of `Picardstack_{X/B}` lying over the identity of `U` — the
points of the inertia stack above it — are the points `𝐆_{m, S}(U)`. -/
@[stacks 0375 "the points of the inertia stack above an object of the Picard stack over T are \
𝐆_{m,S}(T), under the hypothesis that 𝒪_T ⟶ f_{T,*}𝒪_{X_T} is an isomorphism for every test \
scheme T"]
theorem nonempty_vertical_equiv_multiplicativeGroupPoints_of_iso
    (hc : ModulePushforwardCoherence B S hS) (h : s.StructureSheafMapIso) (A : PicardObject s) :
    Nonempty (A.Vertical ≃ multiplicativeGroupPointsAt B S hS A.T.left) :=
  nonempty_vertical_equiv_multiplicativeGroupPoints hc h
    (s.structureUnitsIso_of_structureSheafMapIso) A

/-- Multiplication by an invertible regular function on the test scheme, as an automorphism of
the invertible module of an object of `Picardstack_{X/B}`. -/
def PicardObject.unitsSMulAut (A : PicardObject s)
    (u : (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj A.T.left)))ˣ) :
    A.lineBundle ≅ A.lineBundle where
  hom := (globalFunctionSMul B S hS (s.baseChange A.T)
    (baseChangeGlobalFunctions s.f A.T u)).asHom.app A.lineBundle
  inv := (globalFunctionSMul B S hS (s.baseChange A.T)
    (baseChangeGlobalFunctions s.f A.T ↑u⁻¹)).asHom.app A.lineBundle
  hom_inv_id := by
    rw [globalFunctionSMul_app_comp _ _ _ (baseChangeGlobalFunctions s.f A.T (↑u⁻¹ * ↑u))
      (baseChangeGlobalFunctions_val_mul s.f A.T _ _)]
    exact globalFunctionSMul_app_eq_id _ _ (fun U ↦ by
      rw [Units.inv_mul]; exact baseChangeGlobalFunctions_val_one s.f A.T U) _
  inv_hom_id := by
    rw [globalFunctionSMul_app_comp _ _ _ (baseChangeGlobalFunctions s.f A.T (↑u * ↑u⁻¹))
      (baseChangeGlobalFunctions_val_mul s.f A.T _ _)]
    exact globalFunctionSMul_app_eq_id _ _ (fun U ↦ by
      rw [Units.mul_inv]; exact baseChangeGlobalFunctions_val_one s.f A.T U) _

/-- Under the hypothesis of Stacks 0375, two regular functions on `T` which act in the same way on
an invertible module of `X_T` are equal. -/
private theorem eq_of_globalFunctionSMul_app_eq (h : s.StructureSheafMapIso) (A : PicardObject s)
    {a b : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj A.T.left))}
    (hab : (globalFunctionSMul B S hS (s.baseChange A.T)
        (baseChangeGlobalFunctions s.f A.T a)).asHom.app A.lineBundle =
      (globalFunctionSMul B S hS (s.baseChange A.T)
        (baseChangeGlobalFunctions s.f A.T b)).asHom.app A.lineBundle) : a = b :=
  (bijective_baseChangeGlobalFunctions h A.T).1
    (globalFunctionSMul_injective_of_isInvertibleModule (s.baseChange A.T) A.lineBundle
      A.invertible hab)

/-- **Every automorphism of the invertible module of an object over `T` is multiplication by
exactly one invertible regular function on `T`**, under the hypothesis of Stacks 0375. -/
theorem PicardObject.unitsSMulAut_bijective (h : s.StructureSheafMapIso) (A : PicardObject s) :
    Function.Bijective A.unitsSMulAut := by
  have hπ := (bijective_baseChangeGlobalFunctions h A.T).2
  have hex : ∀ f : A.lineBundle ⟶ A.lineBundle, ∃ c, f = (globalFunctionSMul B S hS
      (s.baseChange A.T) (baseChangeGlobalFunctions s.f A.T c)).asHom.app A.lineBundle := fun f ↦ by
    obtain ⟨b, hb⟩ := exists_eq_globalFunctionSMul_of_isInvertibleModule (s.baseChange A.T)
      A.lineBundle A.invertible f
    obtain ⟨c, hc⟩ := hπ b
    exact ⟨c, hb.trans (by rw [← hc])⟩
  refine ⟨fun u v huv ↦ Units.ext (eq_of_globalFunctionSMul_app_eq h A (congrArg Iso.hom huv)),
    fun α ↦ ?_⟩
  obtain ⟨c, hb₁⟩ := hex α.hom
  obtain ⟨c', hb₂⟩ := hex α.inv
  have h₁ : c' * c = 1 := by
    refine eq_of_globalFunctionSMul_app_eq h A ?_
    rw [← globalFunctionSMul_app_comp _ _ _ _ (baseChangeGlobalFunctions_val_mul s.f A.T c' c),
      ← hb₁, ← hb₂, α.hom_inv_id, globalFunctionSMul_app_eq_id _ _
        (baseChangeGlobalFunctions_val_one s.f A.T)]
  have h₂ : c * c' = 1 := (mul_comm c c').trans h₁
  exact ⟨⟨c, c', h₂, h₁⟩, Iso.ext hb₁.symm⟩

/-- **The `𝐆_m` factor of Stacks 0375 in coordinates.**  Under the hypothesis of Stacks 0375, the
automorphisms of the invertible module of an object of `Picardstack_{X/B}` over `T` are the
points `𝐆_{m, S}(T)`: an automorphism is multiplication by a unique invertible regular function
on `T`, and those are the points of `𝐆_{m, S}` by Stacks 022U. -/
def PicardObject.autEquivMultiplicativeGroupPoints (h : s.StructureSheafMapIso)
    (A : PicardObject s) :
    (A.lineBundle ≅ A.lineBundle) ≃ multiplicativeGroupPointsAt B S hS A.T.left :=
  (Equiv.ofBijective _ (A.unitsSMulAut_bijective h)).symm.trans
    (multiplicativeGroupPointsAtMulEquivUnits B S hS A.T.left).symm.toEquiv

/-! ### Restriction of points of `𝐆_m` is pullback of invertible functions -/

/-- Restriction of points of `𝐆_{m, S}` along a morphism of test schemes is pullback of
invertible regular functions. -/
theorem multiplicativeGroupPresheaf_map_symm {T T' : BigFppfOver B S hS} (g : T ⟶ T')
    (u : (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T')))ˣ) :
    (multiplicativeGroupPresheaf B S hS).map g.op
        ((multiplicativeGroupPointsAtMulEquivUnits B S hS T').symm u) =
      (multiplicativeGroupPointsAtMulEquivUnits B S hS T).symm
        (Units.map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom.toMonoidHom u) := by
  refine (multiplicativeGroupPointsAtMulEquivUnits B S hS T).injective ?_
  rw [MulEquiv.apply_symm_apply]
  have hn := ConcreteCategory.congr_hom ((baseChangePointsIsoGlobalUnits S).hom.naturality
    ((Over.post (X := B.obj hS) B.inclusion).map g).op)
    ((multiplicativeGroupPointsAtMulEquivUnits B S hS T').symm u)
  refine hn.trans ?_
  show Units.map _ ((multiplicativeGroupPointsAtMulEquivUnits B S hS T')
    ((multiplicativeGroupPointsAtMulEquivUnits B S hS T').symm u)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-! ### The coordinates are compatible with the morphisms of the Picard stack -/

/-- **A morphism of `Picardstack_{X/B}` commutes with two automorphisms given by invertible
functions exactly when it pulls the one back to the other.** -/
theorem PicardHom.comp_unitsSMulAut_iff (h : s.StructureSheafMapIso) {A C : PicardObject s}
    (m : PicardHom A C)
    (u : (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj A.T.left)))ˣ)
    (w : (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj C.T.left)))ˣ) :
    PicardHom.comp m (C.verticalOfAut (C.unitsSMulAut w)) =
        PicardHom.comp (A.verticalOfAut (A.unitsSMulAut u)) m ↔
      Units.map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m.base.left).op).hom.toMonoidHom
        w = u := by
  rw [PicardHom.comp_verticalOfAut_eq_iff]
  have hpull := modulePullback_map_globalFunctionSMul (baseChangeMap s.f m.base)
    (baseChangeGlobalFunctions s.f C.T w) _
    (globalFunctionsCompatible_baseChangeGlobalFunctions s.f m.base (w : _)) C.lineBundle
  have hnat := (globalFunctionSMul B S hS (baseChangeSpace s.f A.T)
    (baseChangeGlobalFunctions s.f A.T
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m.base.left).op).hom w))).asHom.naturality
      m.fibre
  have e : (modulePullback B S hS (baseChangeMap s.f m.base)).map (C.unitsSMulAut w).hom ≫
      m.fibre = m.fibre ≫ (globalFunctionSMul B S hS (baseChangeSpace s.f A.T)
        (baseChangeGlobalFunctions s.f A.T
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m.base.left).op).hom w))).asHom.app
            A.lineBundle :=
    (congrArg (fun k ↦ k ≫ m.fibre) hpull).trans hnat.symm
  rw [e]
  constructor
  · intro he
    have he' := ((asIso m.fibre).cancel_iso_hom_left _ _).mp he
    exact Units.ext (eq_of_globalFunctionSMul_app_eq h A he')
  · intro he
    rw [← he]
    rfl

/-- The coordinate of the automorphism given by an invertible function is that function, read as a
point of `𝐆_{m, S}`. -/
theorem PicardObject.autEquivMultiplicativeGroupPoints_unitsSMulAut (h : s.StructureSheafMapIso)
    (A : PicardObject s)
    (u : (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj A.T.left)))ˣ) :
    A.autEquivMultiplicativeGroupPoints h (A.unitsSMulAut u) =
      (multiplicativeGroupPointsAtMulEquivUnits B S hS A.T.left).symm u := by
  simp only [PicardObject.autEquivMultiplicativeGroupPoints, Equiv.trans_apply,
    Equiv.ofBijective_symm_apply_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]

/-- **The coordinates are compatible with the morphisms of `Picardstack_{X/B}`.**  A morphism
`(g, φ)` commutes with the vertical endomorphisms attached to automorphisms `α` and `β` exactly
when the coordinate of `β` restricts along `g` to the coordinate of `α`. -/
theorem PicardHom.comp_verticalOfAut_eq_iff_coordinates (h : s.StructureSheafMapIso)
    {A C : PicardObject s} (m : PicardHom A C) (α : A.lineBundle ≅ A.lineBundle)
    (β : C.lineBundle ≅ C.lineBundle) :
    PicardHom.comp m (C.verticalOfAut β) = PicardHom.comp (A.verticalOfAut α) m ↔
      (multiplicativeGroupPresheaf B S hS).map m.base.left.op
          (C.autEquivMultiplicativeGroupPoints h β) =
        A.autEquivMultiplicativeGroupPoints h α := by
  obtain ⟨uA, rfl⟩ := (A.unitsSMulAut_bijective h).2 α
  obtain ⟨uC, rfl⟩ := (C.unitsSMulAut_bijective h).2 β
  rw [PicardHom.comp_unitsSMulAut_iff h m uA uC,
    PicardObject.autEquivMultiplicativeGroupPoints_unitsSMulAut,
    PicardObject.autEquivMultiplicativeGroupPoints_unitsSMulAut,
    multiplicativeGroupPresheaf_map_symm]
  exact ⟨fun e ↦ congrArg (multiplicativeGroupPointsAtMulEquivUnits B S hS A.T.left).symm e,
    fun e ↦ (multiplicativeGroupPointsAtMulEquivUnits B S hS A.T.left).symm.injective e⟩

/-! ### The coordinates of the inertia of `Picardstack_{X/B}` -/

namespace PicardCategoryData

/-- **The coordinatisation of Stacks 0375 by `𝐆_{m, S}`, compatible with the composition of
`Picardstack_{X/B}`**, for the category of Section 0372, under the hypothesis of Stacks 0375.  On
an object over `T` it is `AlgebraicGeometry.Space.PicardObject.autEquivMultiplicativeGroupPoints`.
-/
def multiplicativeGroupCoordinates (h : s.StructureSheafMapIso) :
    (picardCategoryData (modulePushforwardCoherence B S hS) s).MultiplicativeGroupCoordinates where
  equiv A := Aut.isoEquiv.trans (A.autEquivMultiplicativeGroupPoints h)
  comm {A C} m v w := by
    let : Category.{u + 1} (PicardObject s) :=
      (picardCategoryData (modulePushforwardCoherence B S hS) s).category
    have hv := PicardObject.Vertical.eq_verticalOfAut
      ((picardCategoryData (modulePushforwardCoherence B S hS) s).verticalAutEquivVertical A v)
    have hw := PicardObject.Vertical.eq_verticalOfAut
      ((picardCategoryData (modulePushforwardCoherence B S hS) s).verticalAutEquivVertical C w)
    have key := PicardHom.comp_verticalOfAut_eq_iff_coordinates h m
      (verticalEquivAut (modulePushforwardCoherence B S hS) A
        ((picardCategoryData (modulePushforwardCoherence B S hS) s).verticalAutEquivVertical A v))
      (verticalEquivAut (modulePushforwardCoherence B S hS) C
        ((picardCategoryData (modulePushforwardCoherence B S hS) s).verticalAutEquivVertical C w))
    have e : ∀ {D : PicardObject s}
        (x : (picardCategoryData (modulePushforwardCoherence B S hS) s).siteProjection.VerticalAut
          D),
        (picardCategoryData (modulePushforwardCoherence B S hS) s).verticalAutEquivAut D x =
          Aut.of (verticalEquivAut (modulePushforwardCoherence B S hS) D
            ((picardCategoryData (modulePushforwardCoherence B S hS) s).verticalAutEquivVertical
              D x)) := fun _ ↦ rfl
    rw [e, e]
    rw [← hv, ← hw] at key
    exact key

/-- For the category of Section 0372 and under the hypothesis of Stacks 0375, the coordinates of
Stacks 0375 are compatible with the composition of `Picardstack_{X/B}`, as in Stacks 0DNH. -/
theorem multiplicativeGroupCoordinatesIso (s : PicardSituation B S hS) :
    (picardCategoryData (modulePushforwardCoherence B S hS) s).MultiplicativeGroupCoordinatesIso :=
  fun h ↦ ⟨multiplicativeGroupCoordinates h⟩

end PicardCategoryData

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` such that for
every scheme `T` over `B` the structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the base change
`f_T : X_T ⟶ T` is an isomorphism.  Then the inertia stack of the Picard stack
`Picardstack_{X/B}` of Section 0372 is

`I_{Picardstack_{X/B}} = 𝐆_{m, S} ×_S Picardstack_{X/B}`

as a category over `(Sch/S)_fppf`: the two are equivalent over the big fppf site, by an
equivalence which is the identity on the `Picardstack_{X/B}`-factor and sends a point `(L, α)` of
the inertia over `T` to the point of `𝐆_{m, S}(T) = H^0(T, 𝒪_T^*)` that the automorphism `α` of
`L` is multiplication by.

In Stacks 0375 `f` is a morphism of schemes; here it is a morphism of algebraic spaces, which
contains that case.  "Equal" is read as an equivalence over the site
(`CategoryTheory.StacksRepresentableCFG.EquivalenceOver`), and the product is the 2-fibre product
`CategoryTheory.inertiaPresheafProduct` of the category of elements of `𝐆_{m, S}` with
`Picardstack_{X/B}` over the site. -/
@[stacks 0375 "the inertia stack of the Picard stack is 𝐆_{m,S} ×_S Picardstack_{X/B}, as \
categories over (Sch/S)_fppf, when 𝒪_T ⟶ f_{T,*}𝒪_{X_T} is an isomorphism for every test scheme T"]
theorem nonempty_equivalenceOver_picardInertia_multiplicativeGroupProduct_of_iso
    (s : PicardSituation B S hS) (h : s.StructureSheafMapIso) :
    letI : Category.{u + 1} (PicardObject s) :=
      (picardCategoryData (modulePushforwardCoherence B S hS) s).category
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (relativeInertiaStruct
        (picardCategoryData (modulePushforwardCoherence B S hS) s).siteProjection
        (picardCategoryData (modulePushforwardCoherence B S hS) s).siteProjection)
      (inertiaPresheafProductStruct
        (picardCategoryData (modulePushforwardCoherence B S hS) s).siteProjection
        (multiplicativeGroupPresheaf B S hS))) :=
  ⟨picardInertiaEquivalenceOverMultiplicativeGroupProduct s h⟩

end AlgebraicGeometry.Space

end
