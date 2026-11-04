module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilySheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.TraceCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.BaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.InducedHomBasePoint

/-!
# Characters and base points on the fibres of Laumon's family

Artin–Schreier characters, continuity of representations and geometric points under base change:

* the Artin–Schreier character over `κ` of `φ(g)`, `φ : A → A'` a `k`-algebra map to a
  `κ`-algebra, composed with `ψ ∘ Tr_{κ/k}`, is the one over `k` of `g` composed with `ψ`, along
  homomorphisms `π₁(Y, ȳ) → π₁(Spec A, ·)` induced by `f = Spec φ ∘ β` and by `β`
  (`Stacks.EtaleCohomology.artinSchreierCharacter_trace_baseChange_eq`);
* a representation of `π₁(U, x̄)` whose restriction along `π₁(Z) → π₁(U)` is continuous is
  continuous along every map `π₁(X) → π₁(U)` induced by a morphism `X → U` factoring through `Z`
  (`Stacks.EtaleCohomology.continuous_restrictScalarsRep_comp_of_factor`);
* a geometric point of `𝔸¹_κ` over a geometric point of `U ≅ 𝔸¹_k`, for a finite extension `κ`
  of `k` (`Stacks.EtaleCohomology.exists_geometricPoint_polynomial_map_eq`), and points of the
  geometric fibres of an Artin–Schreier cover
  (`Stacks.ArtinSchreier.nonempty_finiteEtaleFiberFunctor_cover`).

## Main results

* `AlgebraicGeometry.isEtaleFundamentalGroupHomInducedBy_map_cast`.
* `Stacks.EtaleCohomology.artinSchreierCharacter_trace_baseChange_eq`.
* `Stacks.EtaleCohomology.continuous_restrictScalarsRep_comp_of_factor`.
* `Stacks.EtaleCohomology.exists_geometricPoint_polynomial_map_eq`.
* `Stacks.ArtinSchreier.nonempty_finiteEtaleFiberFunctor_cover`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]

/-- **`f_*`, transported along an identification of the base point, is induced by the base change
along `f`.** -/
public theorem isEtaleFundamentalGroupHomInducedBy_map_cast (f : Y ⟶ X) (y : GeometricPoint Y)
    {x : GeometricPoint X} (h : y.map f = x) :
    IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f)
      (h ▸ (etaleFundamentalGroupMap f y).toMonoidHom) := by
  subst h
  exact isEtaleFundamentalGroupHomInducedBy_map f y

end AlgebraicGeometry

namespace Stacks.ArtinSchreier

variable (κ : Type u) [Field κ] [Fintype κ] {A' : Type u} [CommRing A'] [Algebra κ A'] (g : A')

/-- **The geometric fibres of an Artin–Schreier cover are nonempty**: `T^q - T - g(x̄)` has a
root in the algebraically closed residue field of `x̄`. -/
public theorem nonempty_finiteEtaleFiberFunctor_cover (x : GeometricPoint (Spec (.of A'))) :
    Nonempty ((finiteEtaleFiberFunctor x).obj (cover κ A' g)) := by
  let ρ : CommRingCat.of A' ⟶ CommRingCat.of x.residueField := Spec.preimage x.hom
  have hq : 1 < Fintype.card κ := Fintype.one_lt_card
  have hmap : (poly κ g).map ρ.hom = (Polynomial.X : Polynomial x.residueField) ^ Fintype.card κ -
      (Polynomial.X + C (ρ.hom g)) := by
    simp [poly]
  have hdeg : ((poly κ g).map ρ.hom).degree ≠ 0 := by
    rw [hmap, degree_sub_eq_left_of_degree_lt]
    · rw [degree_X_pow]
      exact_mod_cast (show Fintype.card κ ≠ 0 by omega)
    · rw [degree_X_pow, degree_X_add_C]
      exact_mod_cast hq
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg
  have hp : (poly κ g).eval₂ ρ.hom r = 0 := by rwa [← Polynomial.eval_map]
  let lf : Ring κ g →+* x.residueField := AdjoinRoot.lift ρ.hom r hp
  refine ⟨⟨Spec.map (CommRingCat.ofHom lf), ?_⟩⟩
  have hlf : CommRingCat.ofHom (algebraMap A' (Ring κ g)) ≫ CommRingCat.ofHom lf = ρ := by
    ext a
    exact AdjoinRoot.lift_of hp
  show Spec.map (CommRingCat.ofHom lf) ≫ Spec.map (CommRingCat.ofHom (algebraMap A' (Ring κ g))) =
    x.hom
  rw [← Spec.map_comp, hlf, Spec.map_preimage]

end Stacks.ArtinSchreier

namespace Stacks.EtaleCohomology

section Character

variable (k : Type u) [Field k] [Fintype k] (κ : Type u) [Field κ] [Fintype κ] [Algebra k κ]
  {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A'] [Algebra κ A']
  [IsScalarTower k κ A'] [ConnectedSpace (Spec (.of A))] [ConnectedSpace (Spec (.of A'))]

/-- **The Artin–Schreier character of a base change, over an extension of the constants**: for a
`k`-algebra map `φ : A → A'` to a `κ`-algebra, `f = Spec φ ∘ β : Y → Spec A` and homomorphisms
`Φ₁ : π₁(Y, ȳ) → π₁(Spec A, z̄)`, `Φ₂ : π₁(Y, ȳ) → π₁(Spec A', x̄')` induced by the base changes
along `f` and `β`, the character `ψ' ∘ (−χ_{φ(g)})` over `κ` with `ψ' = ψ ∘ Tr_{κ/k}`, read along
`Φ₂`, is the character `ψ ∘ (−χ_g)` over `k`, read along `Φ₁`. -/
public theorem artinSchreierCharacter_trace_baseChange_eq {E : Type} [CommRing E]
    (ψ : AddChar k E) (ψ' : AddChar κ E) (hψ : ∀ a, ψ' a = ψ (Algebra.trace k κ a)) (g : A)
    (φ : A →ₐ[k] A') (g' : A') (hg : φ g = g') (z : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor z).obj (Stacks.ArtinSchreier.cover k A g))
    (x' : GeometricPoint (Spec (.of A')))
    (p₀' : (finiteEtaleFiberFunctor x').obj (Stacks.ArtinSchreier.cover κ A' g'))
    {Y : Scheme.{u}} [ConnectedSpace Y] {yb : GeometricPoint Y} (f : Y ⟶ Spec (.of A))
    (β : Y ⟶ Spec (.of A')) (hf : f = β ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    {Φ₁ : EtaleFundamentalGroup Y yb →* EtaleFundamentalGroup (Spec (.of A)) z}
    {Φ₂ : EtaleFundamentalGroup Y yb →* EtaleFundamentalGroup (Spec (.of A')) x'}
    (hΦ₁ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f) Φ₁)
    (hΦ₂ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange β) Φ₂)
    (γ : EtaleFundamentalGroup Y yb) :
    Stacks.ArtinSchreier.artinSchreierCharacter κ A' g' ψ' x' p₀' (Φ₂ γ) =
      Stacks.ArtinSchreier.artinSchreierCharacter k A g ψ z p₀ (Φ₁ γ) := by
  subst hg
  let q := (finiteEtaleFiberFunctor x').map (Stacks.ArtinSchreier.coverTraceHom k κ (φ g)) p₀'
  have h1 := Stacks.ArtinSchreier.torsorCover_character_coverTraceHom k κ (φ g) x' p₀' (Φ₂ γ)
  have h2 := Stacks.ArtinSchreier.torsorCover_character_map k g φ x' q (Φ₂ γ)
  have h3 := IsEtaleFundamentalGroupHomInducedBy.character_eq_of_eq
    (Stacks.ArtinSchreier.torsorCover k A g) hΦ₁
    (hΦ₂.comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_map (Spec.map (CommRingCat.ofHom φ.toRingHom)) x'))
    hf p₀
    (finiteEtaleFiberProjection (Spec.map (CommRingCat.ofHom φ.toRingHom)) x'
      (Stacks.ArtinSchreier.cover k A g)
      ((finiteEtaleFiberFunctor x').map (Stacks.ArtinSchreier.coverBaseChangeHom k g φ) q)) γ
  apply Units.ext
  rw [Stacks.ArtinSchreier.artinSchreierCharacter_apply,
    Stacks.ArtinSchreier.artinSchreierCharacter_apply, hψ, map_neg]
  have h4 : Algebra.trace k κ (Multiplicative.toAdd
      ((Stacks.ArtinSchreier.torsorCover κ A' (φ g)).character x' p₀' (Φ₂ γ))) =
      Multiplicative.toAdd
        ((Stacks.ArtinSchreier.torsorCover k A' (φ g)).character x' q (Φ₂ γ)) := by
    rw [h1, toAdd_ofAdd]
  rw [h4, h2]
  exact congrArg (fun w => ψ (-Multiplicative.toAdd w)) h3

end Character

section Continuity

variable {X Z U : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Z] [ConnectedSpace U]

/-- **Continuity along a factorisation**: if `Res_b (σ ∘ M)` is continuous for `M : π₁(Z) → π₁(U)`
induced by `g_U : Z → U`, then `Res_b (σ ∘ Φ)` is continuous for every `Φ : π₁(X, x̄') → π₁(U)`
induced by a morphism `X → U` factoring as `g_U ∘ h`: `Φ` is inner conjugate to
`M ∘ t ∘ h_*` for a change of base point `t`. -/
public theorem continuous_restrictScalarsRep_comp_of_factor (h : X ⟶ Z) (gU : Z ⟶ U)
    (gX : X ⟶ U) (hg : h ≫ gU = gX) (x' : GeometricPoint X) {z : GeometricPoint Z}
    {x : GeometricPoint U} {M : EtaleFundamentalGroup Z z →* EtaleFundamentalGroup U x}
    (hM : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange gU) M)
    {Φ : EtaleFundamentalGroup X x' →* EtaleFundamentalGroup U x}
    (hΦ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange gX) Φ)
    {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b (σ.comp M))) :
    Continuous (restrictScalarsRep b (σ.comp Φ)) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso Z z (x'.map h)
  have hΨ := ((isEtaleFundamentalGroupHomInducedBy_map h x').comp_baseChange
    (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t)).comp_baseChange hM
  obtain ⟨c, hc⟩ := hΨ.isInnerConjugate_of_eq hΦ (by rw [Category.comp_id, hg])
  have hcont : Continuous fun γ => restrictScalarsRep b σ c *
      restrictScalarsRep b (σ.comp M)
        (etaleFundamentalGroupBasePointHom t (etaleFundamentalGroupMap h x' γ)) *
      (restrictScalarsRep b σ c)⁻¹ :=
    (continuous_const.mul (hσ.comp ((etaleFundamentalGroupBasePointHom t).continuous.comp
      (etaleFundamentalGroupMap h x').continuous))).mul continuous_const
  convert hcont using 1
  funext γ
  show restrictScalarsRep b σ (Φ γ) = _
  rw [hc γ, map_mul, map_mul, map_inv]
  rfl

end Continuity

section BasePoint

variable {k : Type u} [Field k] {U : Scheme.{u}} (e : U ⟶ Spec (.of (Polynomial k))) [IsIso e]
  (κ : Type u) [Field κ] [Algebra k κ] [Algebra.IsAlgebraic k κ]

/-- **A geometric point of `𝔸¹_κ` over a geometric point of `U ≅ 𝔸¹_k`**, `κ` algebraic over `k`:
a `k`-embedding of `κ` into the algebraically closed residue field. -/
public theorem exists_geometricPoint_polynomial_map_eq (x : GeometricPoint U) :
    ∃ x' : GeometricPoint (Spec (.of (Polynomial κ))),
      x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k κ))) ≫ inv e) =
        x := by
  let ρ : CommRingCat.of (Polynomial k) ⟶ CommRingCat.of x.residueField := Spec.preimage (x.hom ≫ e)
  let iΩ : Algebra k x.residueField := (ρ.hom.comp C).toAlgebra
  let ι : κ →ₐ[k] x.residueField := IsAlgClosed.lift
  let ρ' : Polynomial κ →+* x.residueField := eval₂RingHom ι.toRingHom (ρ.hom Polynomial.X)
  have hρ : CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k κ)) ≫ CommRingCat.ofHom ρ' =
      ρ := by
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show ρ' (Polynomial.map (algebraMap k κ) (C a)) = ρ.hom (C a)
      rw [Polynomial.map_C]
      show eval₂ ι.toRingHom (ρ.hom Polynomial.X) (C (algebraMap k κ a)) = _
      rw [eval₂_C]
      exact ι.commutes a
    · show ρ' (Polynomial.map (algebraMap k κ) Polynomial.X) = ρ.hom Polynomial.X
      rw [Polynomial.map_X]
      exact eval₂_X _ _
  have key : Spec.map (CommRingCat.ofHom ρ') ≫
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k κ))) ≫ inv e) = x.hom := by
    rw [← Category.assoc, ← Spec.map_comp, hρ, Spec.map_preimage, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  refine ⟨⟨x.residueField, Spec.map (CommRingCat.ofHom ρ')⟩, ?_⟩
  show (⟨x.residueField, Spec.map (CommRingCat.ofHom ρ') ≫
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k κ))) ≫ inv e)⟩ :
      GeometricPoint U) = x
  rw [key]

end BasePoint

end Stacks.EtaleCohomology

end
