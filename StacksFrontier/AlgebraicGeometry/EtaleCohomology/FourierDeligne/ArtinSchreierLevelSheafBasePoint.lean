module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BasePointChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeRepresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernelProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalkLinear
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem

/-!
# The lisse sheaves and the Artin–Schreier sheaves at two base points

Let `X` be a connected scheme with geometric points `x̄`, `x̄'` and an isomorphism
`t : F_x̄ ≅ F_x̄'` of the geometric fibre functors (Tag 0BND (2)), with the induced
`φ_t : π₁(X, x̄') → π₁(X, x̄)`. The equivalence of Tag 0DV5 (3) at `x̄`, followed by restriction
along `φ_t`, is the one at `x̄'`
(`AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalenceBasePointIso`): the
equivalence for sheaves of modules is the one for abelian sheaves read on additive functors out
of the one-object category of `Λ`, and the latter is compatible with the change of base point
(`Stacks.EtaleCohomology.finiteLocallyConstantAbelianSheafEquivalenceBasePointIso`). Hence the
lisse sheaf `ℱ_P` built at `x̄` is the lisse sheaf of `P|_{φ_t}` built at `x̄'`
(`Stacks.EtaleCohomology.nonempty_lisseEtaleSheaf_basePoint_iso`).

For the Artin–Schreier character the restriction along `φ_t` of the character at `(x̄, p)` is the
character at `(x̄', p')`, since the character of a torsor cover is invariant under the transport
along `t`. So the sheaf `L_ψ(g)` does not depend on its base point
(`Stacks.ArtinSchreier.nonempty_artinSchreierLevelSheaf_basePoint_iso`). This lets the
Artin–Schreier sheaf of the affine line, built at the origin, be read at the geometric points of
the fibres of `pr₂ : 𝔸¹ × 𝔸¹ → 𝔸¹` in the Artin–Schreier half of the generic coinvariant
vanishing in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalenceBasePointIso`.
* `Stacks.EtaleCohomology.nonempty_lisseEtaleSheaf_basePoint_iso`.
* `Stacks.ArtinSchreier.nonempty_artinSchreierLevelSheaf_basePoint_iso`.
* The inverse image lemmas of `L_ψ` with the base points chosen freely, in the namespace
  `Stacks.ArtinSchreier`:
  * `nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_basePoint`;
  * `nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_constantSheaf_of_basePoint`;
  * `nonempty_tensor_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_basePoint`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Stacks.ConstantSheaf Stacks.GroupCohomology

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {x x' : GeometricPoint X.1}
  (Λ : Type r) [Ring Λ] [Finite Λ]

/-- **Tag 0DV5 (3) at two base points**: the equivalence for finite type locally constant
sheaves of `Λ`-modules at `x̄`, followed by restriction along `π₁(X, x̄') → π₁(X, x̄)`, is the one
at `x̄'`. -/
public def finiteTypeLocallyConstantModuleSheafEquivalenceBasePointIso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor ⋙
        finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupBasePointHom t) ≅
      𝟭 _ ⋙ (finiteTypeLocallyConstantModuleSheafEquivalence B X x' Λ).functor :=
  scalarActionTransportSquare Λ
    ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).symm.trans
      (finiteLocallyConstantModuleSheafScalarActionEquivalence
        (SmallEtale.topology B X.1 X.2) Λ))
    ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).symm.trans
      (finiteLocallyConstantModuleSheafScalarActionEquivalence
        (SmallEtale.topology B X.1 X.2) Λ))
    (finiteTypeContinuousModuleScalarActionEquivalence Λ (EtaleFundamentalGroup X.1 x)).symm
    (finiteTypeContinuousModuleScalarActionEquivalence Λ (EtaleFundamentalGroup X.1 x')).symm
    (P := 𝟭 _) (Pm := 𝟭 _) (Iso.refl _)
    (Equivalence.conjugateSquare
      (finiteTypeContinuousModuleScalarActionEquivalence Λ (EtaleFundamentalGroup X.1 x))
      (finiteTypeContinuousModuleScalarActionEquivalence Λ (EtaleFundamentalGroup X.1 x'))
      (eqToIso (finiteTypeContinuousModuleToScalarAction_res Λ
        (etaleFundamentalGroupBasePointHom t)))).symm
    (Stacks.EtaleCohomology.finiteLocallyConstantAbelianSheafEquivalenceBasePointIso B X t)

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {x x' : GeometricPoint X.1}
  (Λ : Type) [CommRing Λ] [Finite Λ]

/-- **The lisse sheaf `ℱ_P` at `x̄` is the lisse sheaf of `P|_{φ_t}` at `x̄'`**, for an isomorphism
`t : F_x̄ ≅ F_x̄'` of geometric fibre functors. -/
theorem nonempty_lisseEtaleSheaf_basePoint_iso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x')
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    Nonempty ((lisseEtaleSheaf B X x Λ).obj P ≅
      (lisseEtaleSheaf B X x' Λ).obj
        ((finiteTypeContinuousModuleRes.{0, u + 1, u + 1} Λ
          (etaleFundamentalGroupBasePointHom t)).obj P)) := by
  let EX := finiteTypeLocallyConstantModuleSheafEquivalence.{u, 0} B X x Λ
  let EY := finiteTypeLocallyConstantModuleSheafEquivalence.{u, 0} B X x' Λ
  let R := finiteTypeContinuousModuleRes.{0, u + 1, u + 1} Λ (etaleFundamentalGroupBasePointHom t)
  let α := finiteTypeLocallyConstantModuleSheafEquivalenceBasePointIso.{u, 0} B X Λ t
  let G := EX.inverse.obj P
  let β : EY.functor.obj G ≅ R.obj P := (α.app G).symm ≪≫ R.mapIso (EX.counitIso.app P)
  let γ : G ≅ EY.inverse.obj (R.obj P) := EY.unitIso.app G ≪≫ EY.inverse.mapIso β
  exact ⟨(SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor.mapIso
    ((ObjectProperty.ι _).mapIso γ)⟩

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

open Stacks.EtaleCohomology

variable (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A] (g : A)
  [ConnectedSpace (Spec (.of A))] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u}) (hX : schemeSizeBelow B.cutoff (Spec (.of A)))

/-- **`L_ψ(g)` does not depend on its base point**: the Artin–Schreier sheaves built at two
geometric points of the connected `Spec A`, with any points of the fibres of the cover, are
isomorphic. The restriction of the character at `(x̄, p)` along the change of base point is the
character at `(x̄', p')`. -/
theorem nonempty_artinSchreierLevelSheaf_basePoint_iso (x x' : GeometricPoint (Spec (.of A)))
    (p : (finiteEtaleFiberFunctor x).obj (cover k A g))
    (p' : (finiteEtaleFiberFunctor x').obj (cover k A g)) :
    Nonempty (artinSchreierLevelSheaf k A g Λ ψ B hX x p ≅
      artinSchreierLevelSheaf k A g Λ ψ B hX x' p') := by
  have : ConnectedSpace (specObject A B hX).1 := inferInstanceAs (ConnectedSpace (Spec (.of A)))
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso_of_connectedSpace (Spec (.of A)) x x'
  obtain ⟨e⟩ := nonempty_lisseEtaleSheaf_basePoint_iso B (specObject A B hX) Λ t
    (characterContinuousModule Λ (artinSchreierCharacter k A g ψ x p)
      (isOpen_ker_artinSchreierCharacter k A g Λ ψ x p))
  refine ⟨e ≪≫ (lisseEtaleSheaf B (specObject A B hX) x' Λ).mapIso
    (finiteTypeContinuousModuleIsoOfLinearEquiv Λ (LinearEquiv.refl Λ (ULift.{u + 1} Λ))
      fun σ v => ?_)⟩
  have h := (torsorCover k A g).character_etaleFundamentalGroupMulEquiv t p p'
    (etaleFundamentalGroupBasePointHom t σ)
  rw [etaleFundamentalGroupMulEquiv_basePointHom] at h
  show ((artinSchreierCharacter k A g ψ x p (etaleFundamentalGroupBasePointHom t σ) : Λˣ) : Λ) •
      v = ((artinSchreierCharacter k A g ψ x' p' σ : Λˣ) : Λ) • v
  rw [artinSchreierCharacter_apply, artinSchreierCharacter_apply, h]

/-- To map `h⁻¹ L_ψ(g)` to `T` it suffices to do so at a base point lying over `y`, whatever the
point of the fibre of the cover. -/
private theorem nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_forall
    {A' : Type u} [CommRing A'] [Algebra k A'] (φ : A →ₐ[k] A') {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of A))
    {x : GeometricPoint (Spec (.of A))} (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g))
    (y : GeometricPoint (Spec (.of A'))) {T : _}
    (hT : ∀ p₁ : (finiteEtaleFiberFunctor
      (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom)))).obj (cover k A g),
      Nonempty ((etaleModuleInverseImage.{u, 0} Λ h).obj (artinSchreierLevelSheaf k A g Λ ψ B hX
        (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom))) p₁) ≅ T)) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ h).obj
      (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) ≅ T) := by
  obtain ⟨p₁⟩ := nonempty_finiteEtaleFiber_cover k g
    (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom)))
  obtain ⟨a⟩ := nonempty_artinSchreierLevelSheaf_basePoint_iso k A g Λ ψ B hX x _ p₀ p₁
  obtain ⟨b⟩ := hT p₁
  exact ⟨(etaleModuleInverseImage.{u, 0} Λ h).mapIso a ≪≫ b⟩

variable {k g} {A' : Type u} [CommRing A'] [Algebra k A'] (φ : A →ₐ[k] A')
  [ConnectedSpace (Spec (.of A'))] (hX' : schemeSizeBelow B.cutoff (Spec (.of A')))

/-- **T4 (c) at any base points**: `(Spec φ)⁻¹ L_ψ(g) ≅ L_ψ(φ g)`, whatever the base points of the
two Artin–Schreier sheaves. -/
theorem nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_basePoint
    {x : GeometricPoint (Spec (.of A))} (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g))
    (y : GeometricPoint (Spec (.of A')))
    (p₀' : (finiteEtaleFiberFunctor y).obj (cover k A' (φ g))) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
        (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) ≅
      artinSchreierLevelSheaf k A' (φ g) Λ ψ B hX' y p₀') := by
  exact nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_forall k A g Λ ψ B hX
    φ _ p₀ y
    fun p₁ => nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso k g φ Λ ψ B hX hX' y
      p₁ p₀'

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable {Y : Scheme.{u}} (e : Y ⟶ Spec (.of A'))

include hX' in
/-- **`(e ≫ Spec φ)⁻¹ L_ψ(g) ≅ Λ` when `φ g = c^q - c`, at any base point.** -/
theorem nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_constantSheaf_of_basePoint
    (c : A') (hc : φ g = c ^ Fintype.card k - c) {h : Y ⟶ Spec (.of A)}
    (hh : h = e ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    {x : GeometricPoint (Spec (.of A))} (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ h).obj
        (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) ≅
      etaleModuleConstantSheaf Λ (ModuleCat.of Λ (ULift.{u + 1} Λ)) Y) := by
  obtain ⟨z⟩ := (‹ConnectedSpace (Spec (.of A'))›).toNonempty
  let y := GeometricPoint.ofPoint (Spec (.of A')) z
  exact nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_forall k A g Λ ψ B hX
    φ h p₀ y
    fun p₁ => nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_constantSheaf k g φ Λ ψ
      B hX hX' e c hc hh p₁ y rfl

attribute [local instance] etaleModuleInverseImageSheafPullbackMonoidal

include hX' in
/-- **`h₁⁻¹ L ⊗ h₂⁻¹ L ≅ h₃⁻¹ L` at any base point**, for `hᵢ = e ≫ Spec φᵢ` with
`φ₁ g + φ₂ g = φ₃ g`. -/
theorem nonempty_tensor_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_basePoint
    (φ₁ φ₂ φ₃ : A →ₐ[k] A') (hφ : φ₁ g + φ₂ g = φ₃ g) {h₁ h₂ h₃ : Y ⟶ Spec (.of A)}
    (hh₁ : h₁ = e ≫ Spec.map (CommRingCat.ofHom φ₁.toRingHom))
    (hh₂ : h₂ = e ≫ Spec.map (CommRingCat.ofHom φ₂.toRingHom))
    (hh₃ : h₃ = e ≫ Spec.map (CommRingCat.ofHom φ₃.toRingHom))
    {x₁ x₂ x₃ : GeometricPoint (Spec (.of A))} (p₁ : (finiteEtaleFiberFunctor x₁).obj (cover k A g))
    (p₂ : (finiteEtaleFiberFunctor x₂).obj (cover k A g))
    (p₃ : (finiteEtaleFiberFunctor x₃).obj (cover k A g)) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ h₁).obj
          (artinSchreierLevelSheaf k A g Λ ψ B hX x₁ p₁) ⊗
        (etaleModuleInverseImage.{u, 0} Λ h₂).obj
          (artinSchreierLevelSheaf k A g Λ ψ B hX x₂ p₂) ≅
      (etaleModuleInverseImage.{u, 0} Λ h₃).obj
        (artinSchreierLevelSheaf k A g Λ ψ B hX x₃ p₃)) := by
  subst hh₁ hh₂ hh₃
  obtain ⟨z⟩ := (‹ConnectedSpace (Spec (.of A'))›).toNonempty
  let y := GeometricPoint.ofPoint (Spec (.of A')) z
  let I := fun (φ : A →ₐ[k] A') => etaleModuleInverseImage.{u, 0} Λ
    (e ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
  obtain ⟨q₁⟩ := nonempty_finiteEtaleFiber_cover k (φ₁ g) y
  obtain ⟨q₂⟩ := nonempty_finiteEtaleFiber_cover k (φ₂ g) y
  obtain ⟨q₃⟩ := nonempty_finiteEtaleFiber_cover k (φ₃ g) y
  obtain ⟨a₁⟩ :=
    nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_basePoint A Λ ψ B hX
      φ₁ hX' p₁ y q₁
  obtain ⟨a₂⟩ :=
    nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_basePoint A Λ ψ B hX
      φ₂ hX' p₂ y q₂
  obtain ⟨a₃⟩ :=
    nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_basePoint A Λ ψ B hX
      φ₃ hX' p₃ y q₃
  obtain ⟨m⟩ :=
    nonempty_artinSchreierLevelSheaf_tensor_iso_of_add_eq k Λ ψ B hX' _ _ _ hφ y q₁ q₂ q₃
  let J := etaleModuleInverseImage.{u, 0} Λ e
  let c := fun (φ : A →ₐ[k] A') (x : GeometricPoint (Spec (.of A)))
    (p : (finiteEtaleFiberFunctor x).obj (cover k A g)) =>
    (etaleModuleInverseImageCompIso Λ e (Spec.map (CommRingCat.ofHom φ.toRingHom))).app
      (artinSchreierLevelSheaf k A g Λ ψ B hX x p)
  exact ⟨((c φ₁ x₁ p₁ ≪≫ J.mapIso a₁) ⊗ᵢ (c φ₂ x₂ p₂ ≪≫ J.mapIso a₂)) ≪≫
    Functor.Monoidal.μIso J _ _ ≪≫ J.mapIso m ≪≫ (c φ₃ x₃ p₃ ≪≫ J.mapIso a₃).symm⟩

end Stacks.ArtinSchreier

end
