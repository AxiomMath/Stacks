module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Twist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficientInverseImage
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap

/-!
# The inverse image of a twist `ℱ_ρ ⊗ L_ψ(g)`

For a morphism `φ : A → A'` of `𝔽_q`-algebras, the inverse image along `Spec A' → Spec A` of the
`O`-sheaf `ℱ_ρ ⊗ L_ψ(g)` is the `O`-sheaf `ℱ_{ρ ∘ φ_*} ⊗ L_ψ(φ(g))`: the inverse image of the
sheaf of a representation is the sheaf of the composite with the map of fundamental groups
(`Stacks.EtaleCohomology.representationLAdicSheafInverseImageIso`), compatibly with the actions of
`O`, and the Artin–Schreier character of `φ(g)` is that of `g` composed with `φ_*`
(`Stacks.ArtinSchreier.torsorCover_character_map`).

Applied to `A = A₀[t]`, `g = x·t` and the evaluation `A₀[t] → A'` at `c ∈ A'`, this identifies the
fibre at `t = c` of the family `pr₁^*ℱ_ρ ⊗ L_ψ(x·t)` on `U × 𝔸¹` (`U = Spec A₀`) whose `R¹pr₂!`
is Laumon's Fourier transform of `ℱ_ρ`, with the twist `ℱ_ρ ⊗ L_ψ(c·x)` on `U_{A'}`; the
representation is `ρ ∘ pr₁_* ∘ c_*`, which
`AlgebraicGeometry.etaleFundamentalGroupMulEquiv_mapCompIso` compares with `ρ` composed with the
map induced by `Spec A' → U`.

## Main results

* `Stacks.ArtinSchreier.artinSchreierCharacter_map`: `ψ(-χ_{φ(g)}) = ψ(-χ_g) ∘ φ_*`.
* `Stacks.ArtinSchreier.artinSchreierTwistSheafInverseImageIso`,
  `Stacks.ArtinSchreier.artinSchreierTwistSheafInverseImageIso_hom_act`: the isomorphism of
  `O`-sheaves `(Spec φ)⁻¹(ℱ_ρ ⊗ L_ψ(g)) ≅ ℱ_{ρ ∘ φ_*} ⊗ L_ψ(φ(g))`.
* `Stacks.EtaleCohomology.representationCoefficientSheafInverseImageIso`: `f⁻¹ℱ_ρ ≅ ℱ_{ρ'}` for
  any `ρ'` equal to `ρ ∘ f_*`, as `O`-sheaves.
* `Stacks.ArtinSchreier.fourierFamilySheaf`: the family `pr₁^*ℱ_ρ ⊗ L_ψ(x·t)` on `U × 𝔸¹`; its
  fibre at `t = c` is `artinSchreierTwistSheafInverseImageIso` for `g = x·t` and a `k`-algebra map
  `φ : A₀[t] → A'` with `φ(t) = c`, the twist by `L_ψ(c·x)`.

## References

* [G. Laumon, Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil, 1.2]
* [R. Kiehl, R. Weissauer, Weil conjectures, perverse sheaves and ℓ-adic Fourier transform, III.8]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace Y.1] {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [IsNoetherian X.1] [IsNoetherian Y.1]
  (y : GeometricPoint Y.1)
  (ρ : EtaleFundamentalGroup X.1 (y.map f.hom) →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (μ : O →+* Matrix (Fin r) (Fin r) ℤ_[ℓ])
  (hμ : ∀ o g, μ o * (ρ g).val = (ρ g).val * μ o)
  (ρ' : EtaleFundamentalGroup Y.1 y →* GL (Fin r) ℤ_[ℓ]) (hρ' : Continuous ρ')
  (hμ' : ∀ o g, μ o * (ρ' g).val = (ρ' g).val * μ o)
  (h : ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom = ρ')

attribute [local instance] hasWeakSheafify_smallEtale_levels

/-- **The inverse image of the `O`-sheaf of `ρ` is the `O`-sheaf of any representation `ρ'` equal
to `ρ ∘ f_*`** (as ℓ-adic sheaves; the actions of `O` correspond by
`Stacks.EtaleCohomology.representationCoefficientSheafInverseImageIso_hom_act`). It is stated
for any `O`-sheaves `F`, `G` equal to the `O`-sheaves of `ρ` and `ρ'`, so that it applies to
sheaves defined as such (twists) without unfolding them. -/
public def representationCoefficientSheafInverseImageIso
    (F : LAdicSheaf.CoefficientSheaf B X ℓ O)
    (hF : F = representationCoefficientSheaf B X (y.map f.hom) ρ hρ μ hμ)
    (G : LAdicSheaf.CoefficientSheaf B Y ℓ O)
    (hG : G = representationCoefficientSheaf B Y y ρ' hρ' μ hμ') :
    (LAdicSheaf.CoefficientSheaf.inverseImage f F).toLAdicSheaf ≅ G.toLAdicSheaf := by
  subst hF hG h
  exact representationLAdicSheafInverseImageIso B f y ρ hρ

/-- The isomorphism `f⁻¹ℱ_ρ ≅ ℱ_{ρ'}` commutes with the actions of `O`. -/
public theorem representationCoefficientSheafInverseImageIso_hom_act
    (F : LAdicSheaf.CoefficientSheaf B X ℓ O)
    (hF : F = representationCoefficientSheaf B X (y.map f.hom) ρ hρ μ hμ)
    (G : LAdicSheaf.CoefficientSheaf B Y ℓ O)
    (hG : G = representationCoefficientSheaf B Y y ρ' hρ' μ hμ') (o : O) :
    (representationCoefficientSheafInverseImageIso B f y ρ hρ μ hμ ρ' hρ' hμ' h F hF G hG).hom ≫
        (G.act o).asHom =
      ((LAdicSheaf.CoefficientSheaf.inverseImage f F).act o).asHom ≫
        (representationCoefficientSheafInverseImageIso B f y ρ hρ μ hμ ρ' hρ' hμ' h
          F hF G hG).hom := by
  subst hF hG h
  exact representationLAdicSheafInverseImageIso_hom_act B f y ρ hρ μ hμ o

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] {A : Type u} [CommRing A] [Algebra k A] (g : A)
  {A' : Type u} [CommRing A'] [Algebra k A'] (φ : A →ₐ[k] A')
  {O : Type} [CommRing O] (ψ : AddChar k O)

/-- The Artin–Schreier character does not depend on the point of the fibre at which it is read. -/
public theorem artinSchreierCharacter_eq_of_point [ConnectedSpace (Spec (.of A))]
    (x : GeometricPoint (Spec (.of A))) (p₀ p₁ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    artinSchreierCharacter k A g ψ x p₀ = artinSchreierCharacter k A g ψ x p₁ := by
  ext σ
  rw [artinSchreierCharacter_apply, artinSchreierCharacter_apply]
  congr 2
  exact (torsorCover k A g).character_eq_of_smul x p₀ σ p₁
    ((torsorCover k A g).smul_eq_character x p₁ σ p₁)

/-- **The Artin–Schreier character of `φ(g)` is that of `g` composed with
`π₁(Spec A') → π₁(Spec A)`**, read at any points of the fibres. -/
public theorem artinSchreierCharacter_map [ConnectedSpace (Spec (.of A))]
    [ConnectedSpace (Spec (.of A'))] (y : GeometricPoint (Spec (.of A')))
    (p₀' : (finiteEtaleFiberFunctor y).obj (cover k A' (φ g)))
    (p₀ : (finiteEtaleFiberFunctor (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom)))).obj
      (cover k A g)) :
    artinSchreierCharacter k A' (φ g) ψ y p₀' =
      (artinSchreierCharacter k A g ψ (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom))) p₀).comp
        (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) y).toMonoidHom := by
  rw [artinSchreierCharacter_eq_of_point k g ψ _ p₀ (finiteEtaleFiberProjection
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) y (cover k A g)
    ((finiteEtaleFiberFunctor y).map (coverBaseChangeHom k g φ) p₀'))]
  ext σ
  rw [MonoidHom.comp_apply, artinSchreierCharacter_apply, artinSchreierCharacter_apply,
    torsorCover_character_map k g φ y p₀' σ]
  rfl

variable (B : BigEtaleSite.{u}) (hX : schemeSizeBelow B.cutoff (Spec (.of A)))
  (hY : schemeSizeBelow B.cutoff (Spec (.of A')))
  {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[ℓ] O) {r : ℕ}
  [ConnectedSpace (Spec (.of A))] [ConnectedSpace (Spec (.of A'))]

attribute [local instance] hasWeakSheafify_smallEtale_levels

/-- The morphism `Spec A' → Spec A` of the big étale site induced by `φ`. -/
local notation "φS" => (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) :
  specObject A' B hY ⟶ specObject A B hX)

variable (y : GeometricPoint (Spec (.of A')))
  (p₀ : (finiteEtaleFiberFunctor (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom)))).obj
    (cover k A g))
  (p₀' : (finiteEtaleFiberFunctor y).obj (cover k A' (φ g)))
  (ρ : EtaleFundamentalGroup (specObject A B hX).1
    (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom))) →* GL (Fin r) O)
  (hρ : Continuous (restrictScalarsRepresentation B (specObject A B hX)
    (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom))) b ρ))

omit [Fintype k] in
include hρ in
/-- The composite of a continuous representation with the map of fundamental groups is
continuous. -/
public theorem continuous_restrictScalarsRepresentation_comp_map :
    Continuous (restrictScalarsRepresentation B (specObject A' B hY) y b
      (ρ.comp
        (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) y).toMonoidHom)) :=
  hρ.comp (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) y).continuous

/-- The restriction of scalars of `(ρ ⊗ ψ(-χ_g)) ∘ φ_*` is that of `ρ ∘ φ_* ⊗ ψ(-χ_{φ(g)})`. -/
public theorem restrictScalarsRepresentation_artinSchreierTwist_comp :
    (restrictScalarsRepresentation B (specObject A B hX)
        (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom))) b
        (characterTwist ρ (artinSchreierCharacter k A g ψ _ p₀))).comp
          (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) y).toMonoidHom =
      restrictScalarsRepresentation B (specObject A' B hY) y b
        (characterTwist
          (ρ.comp
            (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) y).toMonoidHom)
          (artinSchreierCharacter k A' (φ g) ψ y p₀')) := by
  rw [artinSchreierCharacter_map k g φ ψ y p₀' p₀]
  rfl

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian (Spec (.of A))] [IsNoetherian (Spec (.of A'))]

/-- **The inverse image of `ℱ_ρ ⊗ L_ψ(g)` along `Spec A' → Spec A` is `ℱ_{ρ ∘ φ_*} ⊗ L_ψ(φ(g))`**
(as ℓ-adic sheaves; the actions of `O` correspond by
`Stacks.ArtinSchreier.artinSchreierTwistSheafInverseImageIso_hom_act`). -/
public def artinSchreierTwistSheafInverseImageIso :=
  representationCoefficientSheafInverseImageIso B φS y _
    (continuous_restrictScalarsRepresentation_artinSchreierTwist k A g ψ B hX b _ p₀ ρ hρ)
    (coefficientScalarRingHom b r) (fun o _ => coefficientScalarRingHom_commute b r o _) _
    (continuous_restrictScalarsRepresentation_artinSchreierTwist k A' (φ g) ψ B hY b y p₀' _
      (continuous_restrictScalarsRepresentation_comp_map k φ B hX hY b y ρ hρ))
    (fun o _ => coefficientScalarRingHom_commute b r o _)
    (restrictScalarsRepresentation_artinSchreierTwist_comp k g φ ψ B hX hY b y p₀ p₀' ρ)
    (artinSchreierTwistSheaf k A g ψ B hX b _ p₀ ρ hρ) rfl
    (artinSchreierTwistSheaf k A' (φ g) ψ B hY b y p₀'
      (ρ.comp (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) y).toMonoidHom)
      (continuous_restrictScalarsRepresentation_comp_map k φ B hX hY b y ρ hρ)) rfl

/-- The isomorphism `(Spec φ)⁻¹(ℱ_ρ ⊗ L_ψ(g)) ≅ ℱ_{ρ ∘ φ_*} ⊗ L_ψ(φ(g))` is the general
isomorphism `f⁻¹ℱ_ρ ≅ ℱ_{ρ'}` of the `O`-sheaves of representations. -/
public theorem artinSchreierTwistSheafInverseImageIso_eq :
    artinSchreierTwistSheafInverseImageIso k g φ ψ B hX hY b y p₀ p₀' ρ hρ =
      representationCoefficientSheafInverseImageIso B φS y _
    (continuous_restrictScalarsRepresentation_artinSchreierTwist k A g ψ B hX b _ p₀ ρ hρ)
    (coefficientScalarRingHom b r) (fun o _ => coefficientScalarRingHom_commute b r o _) _
    (continuous_restrictScalarsRepresentation_artinSchreierTwist k A' (φ g) ψ B hY b y p₀' _
      (continuous_restrictScalarsRepresentation_comp_map k φ B hX hY b y ρ hρ))
    (fun o _ => coefficientScalarRingHom_commute b r o _)
    (restrictScalarsRepresentation_artinSchreierTwist_comp k g φ ψ B hX hY b y p₀ p₀' ρ)
    (artinSchreierTwistSheaf k A g ψ B hX b _ p₀ ρ hρ) rfl
    (artinSchreierTwistSheaf k A' (φ g) ψ B hY b y p₀'
          (ρ.comp
            (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) y).toMonoidHom)
          (continuous_restrictScalarsRepresentation_comp_map k φ B hX hY b y ρ hρ)) rfl :=
  rfl

/-- **The isomorphism `(Spec φ)⁻¹(ℱ_ρ ⊗ L_ψ(g)) ≅ ℱ_{ρ ∘ φ_*} ⊗ L_ψ(φ(g))` is `O`-linear.** -/
public theorem artinSchreierTwistSheafInverseImageIso_hom_act (o : O) :
    (artinSchreierTwistSheafInverseImageIso k g φ ψ B hX hY b y p₀ p₀' ρ hρ).hom ≫
        ((artinSchreierTwistSheaf k A' (φ g) ψ B hY b y p₀'
          (ρ.comp
            (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom φ.toRingHom)) y).toMonoidHom)
          (continuous_restrictScalarsRepresentation_comp_map k φ B hX hY b y ρ hρ)).act o).asHom =
      ((LAdicSheaf.CoefficientSheaf.inverseImage φS
          (artinSchreierTwistSheaf k A g ψ B hX b _ p₀ ρ hρ)).act o).asHom ≫
        (artinSchreierTwistSheafInverseImageIso k g φ ψ B hX hY b y p₀ p₀' ρ hρ).hom := by
  rw [artinSchreierTwistSheafInverseImageIso_eq]
  exact representationCoefficientSheafInverseImageIso_hom_act B φS y _ _ _ _ _ _ _ _ _ _ _ _ o

/-! ### The family `pr₁^*ℱ_ρ ⊗ L_ψ(x·t)` on `U × 𝔸¹` and its fibres -/

section Family

variable {A₀ : Type u} [CommRing A₀] [Algebra k A₀] (x : A₀)
  (hU : schemeSizeBelow B.cutoff (Spec (.of A₀)))
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial A₀))))
  [IsNoetherian (Spec (.of A₀))] [IsNoetherian (Spec (.of (Polynomial A₀)))]
  [ConnectedSpace (Spec (.of A₀))] [ConnectedSpace (Spec (.of (Polynomial A₀)))]

/-- **The family `pr₁^*ℱ_ρ ⊗ L_ψ(x·t)` on `U × 𝔸¹`** (`U = Spec A₀`, `t` the coordinate of `𝔸¹`,
`pr₁ : Spec A₀[t] → Spec A₀`): the `O`-sheaf of `ρ ∘ pr₁_*` twisted by the Artin–Schreier sheaf of
`x·t`, the kernel of Laumon's Fourier transform of `ℱ_ρ`. Its inverse image along the map
`Spec A' → U × 𝔸¹` of a `k`-algebra map `φ : A₀[t] → A'` (the fibre at `t = c` for `φ(t) = c`) is
`ℱ_{ρ ∘ pr₁_* ∘ φ_*} ⊗ L_ψ(φ(x)·c)`: `Stacks.ArtinSchreier.artinSchreierTwistSheafInverseImageIso`
with `g = x·t`. -/
public def fourierFamilySheaf (z : GeometricPoint (Spec (.of (Polynomial A₀))))
    (p₀ : (finiteEtaleFiberFunctor z).obj (cover k (Polynomial A₀) (Polynomial.C x * Polynomial.X)))
    (ρ : EtaleFundamentalGroup (specObject A₀ B hU).1
      (z.map (Spec.map (CommRingCat.ofHom
        (IsScalarTower.toAlgHom k A₀ (Polynomial A₀)).toRingHom))) →* GL (Fin r) O)
    (hρ : Continuous (restrictScalarsRepresentation B (specObject A₀ B hU)
      (z.map (Spec.map (CommRingCat.ofHom
        (IsScalarTower.toAlgHom k A₀ (Polynomial A₀)).toRingHom))) b ρ)) :
    LAdicSheaf.CoefficientSheaf B (specObject (Polynomial A₀) B hS) ℓ O :=
  artinSchreierTwistSheaf k (Polynomial A₀) (Polynomial.C x * Polynomial.X) ψ B hS b z p₀
    (ρ.comp (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
      (IsScalarTower.toAlgHom k A₀ (Polynomial A₀)).toRingHom)) z).toMonoidHom)
    (continuous_restrictScalarsRepresentation_comp_map k
      (IsScalarTower.toAlgHom k A₀ (Polynomial A₀)) B hU hS b z ρ hρ)

end Family

end Stacks.ArtinSchreier
