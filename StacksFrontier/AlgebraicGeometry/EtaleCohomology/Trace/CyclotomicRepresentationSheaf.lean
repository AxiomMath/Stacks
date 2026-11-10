module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CyclotomicRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTautologicalSection
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleCofinality

/-!
# `ℱ_{ρ_μ} = μ_n`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure of
`k` separable over `k`, `η̄` a geometric point of `X_k̄` with image `x̄` in `X`, and `n` an integer
invertible in `k`. The cyclotomic representation `ρ_μ = μ_n(k̄)` of `π₁(X, x̄)`
(`AlgebraicGeometry.cyclotomicContinuousModule`) has, as its sheaf `ℱ_{ρ_μ}` (Tag 0DV5 (3), read
through `AlgebraicGeometry.representationSheaf`), the sheaf `μ_n` of `n`-th roots of unity on
`X_étale` (`Stacks.Kummer.rootsOfUnitySheaf`). This file proves it, as an isomorphism of abelian
sheaves on Mathlib's small étale site of `X`.

## Main results

* `AlgebraicGeometry.finiteEtaleOver_hom_ext_of_finiteEtaleFiber`,
  `AlgebraicGeometry.finiteEtaleOverIsoOfFiberEquiv` — morphisms of finite étale covers of a
  connected scheme are determined by their geometric fibres, and an equivariant bijection of
  fibres comes from an isomorphism of covers (Tag 0BND (1)).
* `Stacks.Kummer.isFinite_rootsOfUnityEtaleOver` — the scheme of `n`-th roots of unity is finite.
* `AlgebraicGeometry.cyclotomicRepresentationSheafIso` — **`ℱ_{ρ_μ} ≅ μ_n`**.

## Implementation notes

The sections of `ℱ_ρ` over a general étale `U ⟶ X` are not computable: `ℱ_ρ` is the image of `ρ`
under the inverse of an equivalence, transported across two models of the small étale site. The
comparison is therefore made through representability and the fibre functor. The sheaf of sets
underlying `ℱ_{ρ_μ}` is represented by a finite étale cover `V` with a tautological section `ε`
(`AlgebraicGeometry.representationTautologicalSection`), whose geometric fibre at `x̄` is `μ_n(k̄)`
with its monodromy `ρ_μ` (`AlgebraicGeometry.representationFibreEquiv`). The sheaf `μ_n` is
represented by the base change `W = X ×_k μ_{n,k}` of the finite étale `k`-scheme of `n`-th roots
of unity, with the universal root of unity
(`Stacks.Kummer.isRepresentedBy_rootsOfUnityBaseChangeUniversalSection`). Its geometric fibre at
`x̄` is `μ_n(Ω)`, `Ω` the residue field of `η̄`, which is `μ_n(k̄)` because `k̄` is algebraically
closed; `π₁(X, x̄)` acts on it through `Aut(k̄/k)`
(`AlgebraicGeometry.geometricQuotientGaloisEquiv_spec`), which is `ρ_μ`. The two fibres are
therefore isomorphic as `π₁(X, x̄)`-sets, hence `V ≅ W` (Tag 0BND (1)), and Yoneda turns this into
a bijection `ℱ_{ρ_μ}(U) ≅ μ_n(U)` natural in `U`.

Additivity of that bijection is checked on the universal case. Addition on `ℱ_ρ` is
`ℱ(p₁ + p₂)` on `ℱ(ρ ⊞ ρ)`, `ℱ` being additive; by naturality of the tautological sections it is
induced by the morphism of representing covers attached to `p₁ + p₂`, which acts on fibres by the
addition of `μ_n(k̄)` (`AlgebraicGeometry.representationFibreEquiv_naturality`). On the other
side the product of two roots of unity is induced by the multiplication of `μ_n(Ω)` on fibres. Two
morphisms of finite étale covers that agree on geometric fibres are equal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section FibreLift

variable {S : Scheme.{u}} [ConnectedSpace S] (x : GeometricPoint S)

/-- **Morphisms of finite étale covers of a connected scheme are determined by their geometric
fibres**: the fibre functor of the Galois category of finite étale covers is faithful. -/
theorem finiteEtaleOver_hom_ext_of_finiteEtaleFiber {V W : FiniteEtaleOver S} {f g : V ⟶ W}
    (h : ∀ p : (finiteEtaleFiberFunctor x).obj V,
      (finiteEtaleFiberFunctor x).map f p = (finiteEtaleFiberFunctor x).map g p) : f = g := by
  refine (finiteEtaleEquivalenceOfIsGaloisCategory S x).functor.map_injective ?_
  refine ObjectProperty.hom_ext _ (Action.Hom.ext ?_)
  ext p
  exact h p

/-- **An equivariant bijection of geometric fibres comes from an isomorphism of finite étale
covers** (Tag 0BND (1)): the fibre functor, with the action of `π₁(S, x)`, is an equivalence. -/
def finiteEtaleOverIsoOfFiberEquiv {V W : FiniteEtaleOver S}
    (e : (finiteEtaleFiberFunctor x).obj V ≃ (finiteEtaleFiberFunctor x).obj W)
    (he : ∀ (σ : EtaleFundamentalGroup S x) (p : (finiteEtaleFiberFunctor x).obj V),
      e ((σ.asIso.app V).hom p) = (σ.asIso.app W).hom (e p)) : V ≅ W :=
  (finiteEtaleEquivalenceOfIsGaloisCategory S x).fullyFaithfulFunctor.preimageIso
    (ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.equivEquivIso e) fun σ ↦ by
      ext p
      exact (congrArg e (finiteEtaleEquivalenceOfIsGaloisCategory_action S x V σ p)).trans
        ((he σ p).trans (finiteEtaleEquivalenceOfIsGaloisCategory_action S x W σ (e p)).symm)))

/-- The isomorphism `AlgebraicGeometry.finiteEtaleOverIsoOfFiberEquiv` acts on fibres by `e`. -/
theorem finiteEtaleOverIsoOfFiberEquiv_hom_apply {V W : FiniteEtaleOver S}
    (e : (finiteEtaleFiberFunctor x).obj V ≃ (finiteEtaleFiberFunctor x).obj W)
    (he : ∀ (σ : EtaleFundamentalGroup S x) (p : (finiteEtaleFiberFunctor x).obj V),
      e ((σ.asIso.app V).hom p) = (σ.asIso.app W).hom (e p))
    (p : (finiteEtaleFiberFunctor x).obj V) :
    (finiteEtaleFiberFunctor x).map (finiteEtaleOverIsoOfFiberEquiv x e he).hom p = e p := by
  have h := (finiteEtaleEquivalenceOfIsGaloisCategory S x).fullyFaithfulFunctor.map_preimage
    (ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.equivEquivIso e) fun σ ↦ by
      ext p
      exact (congrArg e (finiteEtaleEquivalenceOfIsGaloisCategory_action S x V σ p)).trans
        ((he σ p).trans (finiteEtaleEquivalenceOfIsGaloisCategory_action S x W σ (e p)).symm))).hom
  exact congrArg (fun φ : (finiteEtaleEquivalenceOfIsGaloisCategory S x).functor.obj V ⟶
      (finiteEtaleEquivalenceOfIsGaloisCategory S x).functor.obj W ↦
        ConcreteCategory.hom φ.hom.hom p) h

end FibreLift

end AlgebraicGeometry

namespace Stacks.Kummer

open _root_.Polynomial

section Finite

variable (Y : Scheme.{u}) (n : ℕ) (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤)))

/-- The standard étale algebra `R[T]/(Tⁿ - 1)` is a finite `R`-module: it is `R[T]/(Tⁿ - 1)`
localized at `1`, and `Tⁿ - 1` is monic. -/
instance moduleFinite_rootsOfUnityPair_ring (R : Type u) [CommRing R] (hn : IsUnit ((n : ℕ) : R)) :
    Module.Finite R (rootsOfUnityPair R n hn).Ring := by
  set P := rootsOfUnityPair R n hn
  have hmonic : P.f.Monic := P.monic_f
  have : Module.Finite R (AdjoinRoot P.f) := hmonic.finite_adjoinRoot
  have hg : AdjoinRoot.mk P.f P.g = 1 := by
    change AdjoinRoot.mk P.f 1 = 1
    exact map_one _
  have : IsLocalization.Away (1 : AdjoinRoot P.f) (Localization.Away (AdjoinRoot.mk P.f P.g)) := by
    rw [← hg]
    infer_instance
  let e : AdjoinRoot P.f ≃ₐ[AdjoinRoot P.f] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    IsLocalization.atOne _ _
  have : Module.Finite R (Localization.Away (AdjoinRoot.mk P.f P.g)) :=
    Module.Finite.of_surjective ((e.toAlgHom.restrictScalars R).toLinearMap) e.surjective
  exact Module.Finite.equiv P.equivAwayAdjoinRoot.symm.toLinearEquiv

/-- **The scheme of `n`-th roots of unity is finite** over `Y`: it is the base change of the
spectrum of the finite algebra `Γ(Y, 𝒪_Y)[T]/(Tⁿ - 1)`. -/
instance isFinite_rootsOfUnityEtaleOver : IsFinite (rootsOfUnityEtaleOver Y n hn).hom := by
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Y, ⊤) (rootsOfUnityPair Γ(Y, ⊤) n hn).Ring))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  change IsFinite (pullback.snd (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(Y, ⊤) (rootsOfUnityPair Γ(Y, ⊤) n hn).Ring))) Y.toSpecΓ)
  infer_instance

/-- **The scheme of `n`-th roots of unity over `Y`, as a finite étale cover of `Y`.** -/
def rootsOfUnityFiniteEtaleOver : FiniteEtaleOver Y :=
  MorphismProperty.Over.mk ⊤ (rootsOfUnityEtaleOver Y n hn).hom ⟨inferInstance, inferInstance⟩

/-- **The geometric fibre of the scheme of `n`-th roots of unity** at a geometric point `s` of `Y`
is the set of `n`-th roots of unity in the global functions of the source of `s`. -/
def rootsOfUnityFiniteEtaleFiberEquiv (s : GeometricPoint Y) :
    finiteEtaleFiber s (rootsOfUnityFiniteEtaleOver Y n hn) ≃
      {x : (Γ(s.source, ⊤))ˣ // x ^ n = 1} :=
  ({ toFun := fun p ↦ CategoryTheory.Over.homMk p.1 p.2
     invFun := fun g ↦ ⟨g.left, CategoryTheory.Over.w g⟩
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl } :
    finiteEtaleFiber s (rootsOfUnityFiniteEtaleOver Y n hn) ≃
      (CategoryTheory.Over.mk s.hom ⟶ rootsOfUnityEtaleOver Y n hn)).trans
    (rootsOfUnityEtaleOverHomEquiv Y n hn (CategoryTheory.Over.mk s.hom))

end Finite

section RootsOfUnityFiber

variable {Z Y : Scheme.{u}} (f : Z ⟶ Y) {n : ℕ} (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
  (x : GeometricPoint Z)

/-- The étale `Z`-scheme `Z ×_Y μ_{n,Y}`, which represents `μ_n` on `Z_étale`
(`Stacks.Kummer.isRepresentedBy_rootsOfUnityBaseChangeUniversalSection`). -/
abbrev rootsOfUnityBaseChangeEtaleObj : Z.Etale :=
  (Stacks.EtaleCohomology.smallEtaleBaseChange f).obj (rootsOfUnityEtaleObj Y n hn)

/-- The root of unity in the global functions of the source of `x` underlying a point of the
geometric fibre of `Z ×_Y μ_{n,Y}` at `x`. -/
def rootsOfUnityBaseChangeFiberEquiv :
    (finiteEtaleFiberFunctor x).obj ((finiteEtaleBaseChange f).obj
        (rootsOfUnityFiniteEtaleOver Y n hn)) ≃ {r : (Γ(x.source, ⊤))ˣ // r ^ n = 1} :=
  (finiteEtaleFiberProjectionEquiv f x _).trans (rootsOfUnityFiniteEtaleFiberEquiv Y n hn (x.map f))

/-- **The root of unity of a fibre point through a morphism into `Z ×_Y μ_{n,Y}`**: a point
`p ≫ k` of the fibre, `p` a lift of `x` to an étale `Z`-scheme `U` and `k : U ⟶ Z ×_Y μ_{n,Y}`,
carries the pullback along `p` of the root of unity on `U` corresponding to `k`. -/
theorem rootsOfUnityBaseChangeFiberEquiv_eq {U : Z.Etale}
    (k : U ⟶ rootsOfUnityBaseChangeEtaleObj f hn) (p : x.source ⟶ U.left) (hp : p ≫ U.hom = x.hom)
    (q : (finiteEtaleFiberFunctor x).obj ((finiteEtaleBaseChange f).obj
      (rootsOfUnityFiniteEtaleOver Y n hn))) (hq : q.1 = p ≫ k.left) :
    (rootsOfUnityBaseChangeFiberEquiv f hn x q).1 =
      Units.map p.appTop.hom.toMonoidHom (rootsOfUnityEtaleBaseChangeHomEquiv f n hn U k).1 := by
  let g : CategoryTheory.Over.mk (x.map f).hom ⟶
      (CategoryTheory.Over.map f).obj ((Scheme.Etale.forget Z).obj U) :=
    CategoryTheory.Over.homMk p (by
      change p ≫ U.hom ≫ f = x.hom ≫ f
      rw [← Category.assoc, hp])
  refine rootsOfUnityEtaleOverHomEquiv_map_left Y n hn g _ _ ?_
  refine (congrArg (· ≫ pullback.fst _ f) hq).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (p ≫ ·) ?_)
  exact (mapPullbackAdj_homEquiv_symm_left f ((Scheme.Etale.forget Z).map k)).symm

variable (Z) in
omit hn in
/-- The `n`-th root of unity underlying a section of `μ_n`, on a sum of sections: it is the
product. -/
theorem rootsOfUnitySection_add (n : ℕ) (U : Z.Etaleᵒᵖ)
    (a b : ToType ((rootsOfUnitySheaf.{u, 0} Z n).obj.obj U)) :
    (rootsOfUnitySection.{u, 0} Z n U (a + b)).1 =
      (rootsOfUnitySection.{u, 0} Z n U a).1 * (rootsOfUnitySection.{u, 0} Z n U b).1 := by
  change Additive.toMul (((rootsOfUnityι.{u, 0} Z n).hom.app U (a + b)).down) = _
  rw [map_add]
  rfl

/-- **The section of `μ_n` corresponding to a morphism into `Z ×_Y μ_{n,Y}`** is the root of unity
attached to that morphism. -/
theorem rootsOfUnitySection_map_rootsOfUnityBaseChangeUniversalSection {U : Z.Etale}
    (k : U ⟶ rootsOfUnityBaseChangeEtaleObj f hn) :
    rootsOfUnitySection.{u, 0} Z n (op U) ((rootsOfUnitySheaf.{u, 0} Z n).obj.map k.op
        (rootsOfUnityBaseChangeUniversalSection.{u, 0} f n hn)) =
      rootsOfUnityEtaleBaseChangeHomEquiv f n hn U k := by
  refine Subtype.ext ((rootsOfUnitySection_naturality.{u, 0} Z n k _).trans ?_)
  have hu : rootsOfUnitySection.{u, 0} Z n (op (rootsOfUnityBaseChangeEtaleObj f hn))
      (rootsOfUnityBaseChangeUniversalSection.{u, 0} f n hn) =
        rootsOfUnityEtaleBaseChangeHomEquiv f n hn _ (𝟙 _) :=
    (rootsOfUnitySectionsEquiv.{u, 0} Z n _).apply_symm_apply _
  rw [hu]
  refine Eq.trans ?_ (congrArg (fun z ↦ (rootsOfUnityEtaleBaseChangeHomEquiv f n hn U z).1)
    (Category.comp_id k))
  exact (rootsOfUnityEtaleBaseChangeHomEquiv_naturality f n hn k (𝟙 _)).symm

end RootsOfUnityFiber

end Stacks.Kummer

namespace AlgebraicGeometry

open Stacks.Kummer Stacks.Frobenius Stacks.EtaleCohomology Stacks.GroupCohomology _root_.Polynomial

section Cyclotomic

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]

/-- The geometric point `x̄` of `X`: the image of the geometric point `η̄` of `X_k̄`. -/
abbrev curveGeometricBasePoint : GeometricPoint X.1 :=
  y.map (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom

omit [NeZero n] in
/-- An integer invertible in `k` is invertible in the global functions of `Spec k`. -/
theorem isUnit_natCast_ΓSpec_of_isUnit (hn : IsUnit (n : k)) :
    IsUnit ((n : ℕ) : Γ(Spec (.of k), ⊤)) := by
  simpa using hn.map (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The ring map `k̄ → Γ(Spec Ω, 𝒪)`, `Ω` the residue field of the geometric point `η̄` of `X_k̄`,
induced by `Spec Ω ⟶ X_k̄ ⟶ Spec k̄`. -/
abbrev geometricPointResidueRingHom : kbar →+* Γ(y.source, ⊤) :=
  ((Scheme.ΓSpecIso (.of kbar)).inv ≫ (geometricPointToSpec B X f kbar y).appTop).hom

omit [IsCurve k f] [Smooth f] [GeometricallyConnected f] [IsAlgClosed kbar]
  [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar] in
/-- The ring map `geometricPointResidueRingHom` from `k̄` to `Γ(Spec Ω, 𝒪)` is injective. -/
theorem injective_geometricPointResidueRingHom :
    Function.Injective (geometricPointResidueRingHom B X f kbar y) := by
  have : Nontrivial Γ(y.source, ⊤) :=
    (Scheme.ΓSpecIso (.of y.residueField)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  exact (geometricPointResidueRingHom B X f kbar y).injective

omit [IsCurve k f] [Smooth f] [GeometricallyConnected f] [Algebra.IsAlgebraic k kbar]
  [Algebra.IsSeparable k kbar] in
/-- **`μ_n(k̄) = μ_n(Ω)`**: the map `k̄ → Γ(Spec Ω, 𝒪) ≅ Ω` is a bijection on `n`-th roots of
unity, `k̄` being algebraically closed: `Tⁿ - 1` splits over `k̄`, so every root of it in `Ω`
comes from `k̄`. -/
theorem bijective_geometricPointRootsOfUnity :
    Function.Bijective (fun ζ : _root_.rootsOfUnity n kbar ↦
      (⟨Units.map (geometricPointResidueRingHom B X f kbar y).toMonoidHom ζ, by
        rw [← map_pow, (mem_rootsOfUnity n (ζ : kbarˣ)).mp ζ.2, map_one]⟩ :
        {x : (Γ(y.source, ⊤))ˣ // x ^ n = 1})) := by
  set φ := geometricPointResidueRingHom B X f kbar y
  have hφ : Function.Injective φ := injective_geometricPointResidueRingHom B X f kbar y
  refine ⟨fun ζ ξ h ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · have h' := congrArg
      (fun z : {x : (Γ(y.source, ⊤))ˣ // x ^ n = 1} ↦ ((z.1 : _) : Γ(y.source, ⊤))) h
    exact Subtype.ext (Units.ext (hφ h'))
  · let e := (Scheme.ΓSpecIso (.of y.residueField)).commRingCatIsoToRingEquiv
    let ψ : kbar →+* y.residueField := (e : Γ(y.source, ⊤) →+* y.residueField).comp φ
    have hψ : Function.Injective ψ := e.injective.comp hφ
    have hroot :
        ((Polynomial.X ^ n - 1 : Polynomial kbar).map ψ).IsRoot (e (x : Γ(y.source, ⊤))) := by
      have hx' : (e (x : Γ(y.source, ⊤))) ^ n = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, map_one]
      simp [hx']
    have hne : (Polynomial.X ^ n - 1 : Polynomial kbar) ≠ 0 := by
      simpa using Polynomial.X_pow_sub_C_ne_zero (NeZero.pos n) (1 : kbar)
    obtain ⟨z, hz⟩ :=
      (IsAlgClosed.splits (Polynomial.X ^ n - 1 : Polynomial kbar)).mem_range_of_isRoot hne hroot
    have hzn : z ^ n = 1 := hψ (by
      rw [map_pow, hz, map_one, ← map_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one,
        map_one])
    refine ⟨rootsOfUnity.mkOfPowEq z hzn, Subtype.ext (Units.ext (e.injective ?_))⟩
    change ψ ((rootsOfUnity.mkOfPowEq z hzn : kbarˣ) : kbar) = _
    rwa [rootsOfUnity.coe_mkOfPowEq]

/-- `μ_n(k̄) ≃ μ_n(Γ(Spec Ω, 𝒪))`, by `AlgebraicGeometry.bijective_geometricPointRootsOfUnity`. -/
def geometricPointRootsOfUnityEquiv :
    _root_.rootsOfUnity n kbar ≃ {x : (Γ(y.source, ⊤))ˣ // x ^ n = 1} :=
  Equiv.ofBijective _ (bijective_geometricPointRootsOfUnity B X f kbar y n)

omit [IsCurve k f] [Smooth f] [GeometricallyConnected f] [Algebra.IsAlgebraic k kbar]
  [Algebra.IsSeparable k kbar] in
/-- `geometricPointRootsOfUnityEquiv` sends `ζ` to its image under
`geometricPointResidueRingHom`. -/
theorem geometricPointRootsOfUnityEquiv_apply_coe (ζ : _root_.rootsOfUnity n kbar) :
    (((geometricPointRootsOfUnityEquiv B X f kbar y n ζ).1 : (Γ(y.source, ⊤))ˣ) : Γ(y.source, ⊤)) =
      geometricPointResidueRingHom B X f kbar y ((ζ : kbarˣ) : kbar) :=
  rfl

variable {n} (hnk : IsUnit ((n : ℕ) : Γ(Spec (.of k), ⊤)))

omit [NeZero n] in
/-- **The `k̄`-point of the `k`-scheme `μ_{n,k}` attached to `ζ ∈ μ_n(k̄)`.** -/
def rootsOfUnityKbarPoint (ζ : _root_.rootsOfUnity n kbar) :
    CategoryTheory.Over.mk (specAlgebraMap k kbar) ⟶ rootsOfUnityEtaleOver (Spec (.of k)) n hnk :=
  (rootsOfUnityEtaleOverHomEquiv _ n hnk _).symm
    ⟨Units.map (Scheme.ΓSpecIso (.of kbar)).inv.hom.toMonoidHom ζ, by
      rw [← map_pow, (mem_rootsOfUnity n (ζ : kbarˣ)).mp ζ.2, map_one]⟩

omit [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar] [NeZero n] in
/-- **Galois acts on `k̄`-points of `μ_{n,k}` through its action on roots of unity**: the point
attached to `σ(ζ)` is the point attached to `ζ` precomposed with `Spec σ`. -/
theorem rootsOfUnityKbarPoint_galois (σ : kbar ≃ₐ[k] kbar) (ζ : _root_.rootsOfUnity n kbar) :
    (rootsOfUnityKbarPoint kbar hnk (galoisRootsOfUnity k kbar n σ ζ)).left =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        (rootsOfUnityKbarPoint kbar hnk ζ).left := by
  have hw : Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ specAlgebraMap k kbar =
      specAlgebraMap k kbar := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact σ.commutes a
  let g : CategoryTheory.Over.mk (specAlgebraMap k kbar) ⟶
      CategoryTheory.Over.mk (specAlgebraMap k kbar) :=
    CategoryTheory.Over.homMk (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) hw
  let k' : CategoryTheory.Over.mk (specAlgebraMap k kbar) ⟶
      rootsOfUnityEtaleOver (Spec (.of k)) n hnk :=
    CategoryTheory.Over.homMk (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
      (rootsOfUnityKbarPoint kbar hnk ζ).left) (by
        rw [Category.assoc, CategoryTheory.Over.w (rootsOfUnityKbarPoint kbar hnk ζ)]
        exact hw)
  have h :=
    rootsOfUnityEtaleOverHomEquiv_map_left _ n hnk g (rootsOfUnityKbarPoint kbar hnk ζ) k' rfl
  suffices hk : rootsOfUnityKbarPoint kbar hnk (galoisRootsOfUnity k kbar n σ ζ) = k' from
    congrArg CommaMorphism.left hk
  apply (rootsOfUnityEtaleOverHomEquiv _ n hnk _).injective
  refine Subtype.ext (h.trans ?_).symm
  simp only [rootsOfUnityKbarPoint, Equiv.apply_symm_apply]
  apply Units.ext
  change (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)).appTop.hom
      ((Scheme.ΓSpecIso (.of kbar)).inv.hom ((ζ : kbarˣ) : kbar)) =
    (Scheme.ΓSpecIso (.of kbar)).inv.hom (σ ((ζ : kbarˣ) : kbar))
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ.toAlgHom.toRingHom)) _).symm

/-- The finite étale `k`-scheme `μ_{n,k}`. -/
abbrev cyclotomicCover : FiniteEtaleOver (Spec (.of k)) :=
  rootsOfUnityFiniteEtaleOver (Spec (.of k)) n hnk

/-- The point `Spec Ω ⟶ Spec k̄ ⟶ μ_{n,k}` of the geometric fibre of `μ_{n,k}` at the image of
`η̄` in `Spec k`, attached to `ζ ∈ μ_n(k̄)`. -/
def cyclotomicCoverPoint (ζ : _root_.rootsOfUnity n kbar) :
    letI := connectedSpace_of_isCurve B X f
    finiteEtaleFiber ((y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom).map f) (cyclotomicCover hnk) :=
  ⟨geometricPointToSpec B X f kbar y ≫ (rootsOfUnityKbarPoint kbar hnk ζ).left, by
    change (geometricPointToSpec B X f kbar y ≫ (rootsOfUnityKbarPoint kbar hnk ζ).left) ≫
      (rootsOfUnityEtaleOver (Spec (.of k)) n hnk).hom = _
    rw [Category.assoc, CategoryTheory.Over.w (rootsOfUnityKbarPoint kbar hnk ζ)]
    exact geometricPointToSpec_comp_specAlgebraMap B X f kbar y⟩

omit [Smooth f] [GeometricallyConnected f] [Algebra.IsSeparable k kbar] in
/-- The root of unity in `Γ(Spec Ω, 𝒪)` underlying the point attached to `ζ` is the image of
`ζ`. -/
theorem rootsOfUnityFiniteEtaleFiberEquiv_cyclotomicCoverPoint (ζ : _root_.rootsOfUnity n kbar) :
    rootsOfUnityFiniteEtaleFiberEquiv (Spec (.of k)) n hnk _
        (cyclotomicCoverPoint B X f kbar y hnk ζ) =
      geometricPointRootsOfUnityEquiv B X f kbar y n ζ := by
  let g : CategoryTheory.Over.mk ((y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom).map f).hom ⟶
      CategoryTheory.Over.mk (specAlgebraMap k kbar) :=
    CategoryTheory.Over.homMk (geometricPointToSpec B X f kbar y)
      (geometricPointToSpec_comp_specAlgebraMap B X f kbar y)
  have h := rootsOfUnityEtaleOverHomEquiv_map_left _ n hnk g (rootsOfUnityKbarPoint kbar hnk ζ)
    (CategoryTheory.Over.homMk (cyclotomicCoverPoint B X f kbar y hnk ζ).1
      (cyclotomicCoverPoint B X f kbar y hnk ζ).2) rfl
  refine Subtype.ext (h.trans ?_)
  rw [rootsOfUnityKbarPoint, Equiv.apply_symm_apply]
  exact Units.ext rfl

/-- **The geometric fibre of `W = X ×_k μ_{n,k}` at `x̄` is `μ_n(k̄)`.** -/
def cyclotomicFiberEquiv :
    letI := connectedSpace_of_isCurve B X f
    _root_.rootsOfUnity n kbar ≃ (finiteEtaleFiberFunctor (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)).obj
        ((finiteEtaleBaseChange f).obj (cyclotomicCover hnk)) :=
  (geometricPointRootsOfUnityEquiv B X f kbar y n).trans
    ((rootsOfUnityFiniteEtaleFiberEquiv (Spec (.of k)) n hnk
        ((curveGeometricBasePoint B X f kbar y).map f)).symm.trans
      (finiteEtaleFiberProjectionEquiv f (curveGeometricBasePoint B X f kbar y)
        (cyclotomicCover hnk)).symm)

omit [Smooth f] [GeometricallyConnected f] [Algebra.IsSeparable k kbar] in
/-- The image of the fibre point `cyclotomicFiberEquiv ζ` of `X ×_k μ_{n,k}` under the projection
to the geometric fibre of `μ_{n,k}` is `cyclotomicCoverPoint ζ`. -/
theorem finiteEtaleFiberProjection_cyclotomicFiberEquiv (ζ : _root_.rootsOfUnity n kbar) :
    finiteEtaleFiberProjection f (curveGeometricBasePoint B X f kbar y) (cyclotomicCover hnk)
        (cyclotomicFiberEquiv B X f kbar y hnk ζ) =
      cyclotomicCoverPoint B X f kbar y hnk ζ := by
  change finiteEtaleFiberProjectionEquiv f (curveGeometricBasePoint B X f kbar y)
    (cyclotomicCover hnk) ((finiteEtaleFiberProjectionEquiv f _ _).symm _) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_eq,
    rootsOfUnityFiniteEtaleFiberEquiv_cyclotomicCoverPoint]

omit [Smooth f] in
/-- **The monodromy on the geometric fibre of `W = X ×_k μ_{n,k}` is `ρ_μ`**: `γ ∈ π₁(X, x̄)`
acts on `μ_n(k̄)` through its image in `Aut(k̄/k)`. -/
theorem cyclotomicFiberEquiv_smul
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (ζ : _root_.rootsOfUnity n kbar) :
    (γ.asIso.app ((finiteEtaleBaseChange f).obj (cyclotomicCover hnk))).hom
        (cyclotomicFiberEquiv B X f kbar y hnk ζ) =
      cyclotomicFiberEquiv B X f kbar y hnk
        (galoisRootsOfUnity k kbar n (geometricGaloisProjection B X f kbar y γ) ζ) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  apply (finiteEtaleFiberProjectionEquiv f _ (cyclotomicCover hnk)).injective
  change finiteEtaleFiberProjection f _ _ _ = finiteEtaleFiberProjection f _ _ _
  rw [etaleFundamentalGroupMap_finiteEtaleFiberProjection,
    finiteEtaleFiberProjection_cyclotomicFiberEquiv,
    finiteEtaleFiberProjection_cyclotomicFiberEquiv]
  refine Subtype.ext ?_
  refine (geometricQuotientGaloisEquiv_spec B X f kbar y γ (cyclotomicCover hnk)
    (rootsOfUnityKbarPoint kbar hnk ζ).left
    (CategoryTheory.Over.w (rootsOfUnityKbarPoint kbar hnk ζ))
    (cyclotomicCoverPoint B X f kbar y hnk ζ) rfl).trans ?_
  change _ = geometricPointToSpec B X f kbar y ≫ (rootsOfUnityKbarPoint kbar hnk _).left
  rw [rootsOfUnityKbarPoint_galois]
  rfl

end Cyclotomic

section Comparison

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) {n : ℕ} [NeZero n]
  (hnk : IsUnit ((n : ℕ) : Γ(Spec (.of k), ⊤)))

/-- **Every section of `ℱ_ρ` is the restriction of the tautological section along a unique
morphism into the representing cover.** -/
theorem bijective_map_representationTautologicalSection {X : B.Scheme} [ConnectedSpace X.1]
    (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (U : X.1.Etale) :
    Function.Bijective (fun t : U ⟶ representationCover B X x Λ ρ ↦
      ((representationSheaf B X x Λ).obj ρ).obj.map t.op
        (representationTautologicalSection B X x Λ ρ)) :=
  bijective_map_of_isIso_sectionEquiv_symm _ _
    (isIso_sectionEquiv_symm_representationTautologicalSection B X x Λ ρ) U

/-- The underlying set of `ρ_μ` is `μ_n(k̄)`. -/
def cyclotomicContinuousModuleEquiv :
    (cyclotomicContinuousModule B X f kbar y n).obj.obj.obj.V ≃ _root_.rootsOfUnity n kbar :=
  Equiv.ulift.trans Additive.toMul

omit [Smooth f] in
/-- Under `AlgebraicGeometry.cyclotomicContinuousModuleEquiv`, `γ` acts on `μ_n(k̄)` through its
image in `Aut(k̄/k)`. -/
theorem cyclotomicContinuousModuleEquiv_ρ
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (curveGeometricBasePoint B X f kbar y))
    (m : (cyclotomicContinuousModule B X f kbar y n).obj.obj.obj.V) :
    cyclotomicContinuousModuleEquiv B X f kbar y
        (((cyclotomicContinuousModule B X f kbar y n).obj.obj.obj.ρ γ).asHom.hom m) =
      galoisRootsOfUnity k kbar n (geometricGaloisProjection B X f kbar y γ)
        (cyclotomicContinuousModuleEquiv B X f kbar y m) :=
  rfl

omit [Smooth f] in
/-- Addition on `ρ_μ` is multiplication of roots of unity. -/
theorem cyclotomicContinuousModuleEquiv_add
    (a b : (cyclotomicContinuousModule B X f kbar y n).obj.obj.obj.V) :
    cyclotomicContinuousModuleEquiv B X f kbar y (a + b) =
      cyclotomicContinuousModuleEquiv B X f kbar y a *
        cyclotomicContinuousModuleEquiv B X f kbar y b :=
  rfl

/-- **The fibre at `x̄` of the cover representing `ℱ_{ρ_μ}` is `μ_n(k̄)`**
(`AlgebraicGeometry.representationFibreEquiv`). -/
def cyclotomicRepresentationFiberRoot :
    letI := connectedSpace_of_isCurve B X f
    (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).obj
        (representationFiniteEtaleCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n)
          (cyclotomicContinuousModule B X f kbar y n)) ≃ _root_.rootsOfUnity n kbar :=
  let := connectedSpace_of_isCurve B X f
  (representationFibreEquiv B X _ (ZMod n) (cyclotomicContinuousModule B X f kbar y n)).trans
    (cyclotomicContinuousModuleEquiv B X f kbar y)

omit [Smooth f] in
/-- `AlgebraicGeometry.cyclotomicRepresentationFiberRoot` intertwines the monodromy with the action
of `π₁(X, x̄)` on `μ_n(k̄)` through `Aut(k̄/k)`. -/
theorem cyclotomicRepresentationFiberRoot_smul
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (curveGeometricBasePoint B X f kbar y))
    (v : letI := connectedSpace_of_isCurve B X f
      (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).obj
        (representationFiniteEtaleCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n)
          (cyclotomicContinuousModule B X f kbar y n))) :
    cyclotomicRepresentationFiberRoot B X f kbar y ((γ.asIso.app _).hom v) =
      galoisRootsOfUnity k kbar n (geometricGaloisProjection B X f kbar y γ)
        (cyclotomicRepresentationFiberRoot B X f kbar y v) := by
  let := connectedSpace_of_isCurve B X f
  have h := representationFibreEquiv_smul B X _ (ZMod n) (cyclotomicContinuousModule B X f kbar y n)
    γ v
  rw [finiteTypeContinuousModuleRepresentation_apply] at h
  unfold cyclotomicRepresentationFiberRoot
  rw [Equiv.trans_apply, Equiv.trans_apply, h]
  exact cyclotomicContinuousModuleEquiv_ρ B X f kbar y γ _

omit [Smooth f] in
/-- `AlgebraicGeometry.cyclotomicRepresentationFiberRoot` is natural along morphisms `ρ₂ ⟶ ρ_μ`. -/
theorem cyclotomicRepresentationFiberRoot_naturality
    {ρ₂ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n)
        (EtaleFundamentalGroup X.1 (curveGeometricBasePoint B X f kbar y))}
    (φ : ρ₂ ⟶ cyclotomicContinuousModule B X f kbar y n)
    (v : letI := connectedSpace_of_isCurve B X f
      (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).obj
        (representationFiniteEtaleCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n) ρ₂)) :
    letI := connectedSpace_of_isCurve B X f
    cyclotomicRepresentationFiberRoot B X f kbar y
        ((finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).map
          ((representingCover B X).map ((representationSetSheaf B X
            (curveGeometricBasePoint B X f kbar y) (ZMod n)).map φ)) v) =
      cyclotomicContinuousModuleEquiv B X f kbar y
        (φ.hom.hom.hom.hom.hom (representationFibreEquiv B X
          (curveGeometricBasePoint B X f kbar y) (ZMod n) ρ₂ v)) := by
  let := connectedSpace_of_isCurve B X f
  have h := representationFibreEquiv_naturality B X (curveGeometricBasePoint B X f kbar y)
    (ZMod n) φ v
  unfold cyclotomicRepresentationFiberRoot
  rw [Equiv.trans_apply, h]

/-- **The fibre at `x̄` of the cover representing `ℱ_{ρ_μ}` is that of `X ×_k μ_{n,k}`**: both are
`μ_n(k̄)`, by `AlgebraicGeometry.cyclotomicRepresentationFiberRoot` and
`AlgebraicGeometry.cyclotomicFiberEquiv`. -/
def cyclotomicRepresentationFiberEquiv :
    letI := connectedSpace_of_isCurve B X f
    (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).obj
        (representationFiniteEtaleCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n)
          (cyclotomicContinuousModule B X f kbar y n)) ≃
      (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).obj
        ((finiteEtaleBaseChange f).obj (cyclotomicCover hnk)) :=
  (cyclotomicRepresentationFiberRoot B X f kbar y).trans (cyclotomicFiberEquiv B X f kbar y hnk)

omit [Smooth f] in
/-- `cyclotomicRepresentationFiberEquiv` is `cyclotomicFiberEquiv` applied after
`cyclotomicRepresentationFiberRoot`. -/
theorem cyclotomicRepresentationFiberEquiv_apply
    (v : letI := connectedSpace_of_isCurve B X f
      (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).obj
        (representationFiniteEtaleCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n)
          (cyclotomicContinuousModule B X f kbar y n))) :
    cyclotomicRepresentationFiberEquiv B X f kbar y hnk v =
      cyclotomicFiberEquiv B X f kbar y hnk (cyclotomicRepresentationFiberRoot B X f kbar y v) :=
  Equiv.trans_apply _ _ _

omit [Smooth f] in
/-- `AlgebraicGeometry.cyclotomicRepresentationFiberEquiv` intertwines the monodromy actions. -/
theorem cyclotomicRepresentationFiberEquiv_smul
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (curveGeometricBasePoint B X f kbar y))
    (v : letI := connectedSpace_of_isCurve B X f
      (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).obj
        (representationFiniteEtaleCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n)
          (cyclotomicContinuousModule B X f kbar y n))) :
    cyclotomicRepresentationFiberEquiv B X f kbar y hnk ((γ.asIso.app _).hom v) =
      (γ.asIso.app _).hom (cyclotomicRepresentationFiberEquiv B X f kbar y hnk v) := by
  let := connectedSpace_of_isCurve B X f
  simp only [cyclotomicRepresentationFiberEquiv, Equiv.trans_apply]
  rw [cyclotomicRepresentationFiberRoot_smul]
  exact (cyclotomicFiberEquiv_smul B X f kbar y hnk γ _).symm

/-- **The cover representing `ℱ_{ρ_μ}` is `X ×_k μ_{n,k}`**, as finite étale covers of `X`
(Tag 0BND (1)). -/
def cyclotomicRepresentationCoverIso :
    letI := connectedSpace_of_isCurve B X f
    representationFiniteEtaleCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n)
        (cyclotomicContinuousModule B X f kbar y n) ≅
      (finiteEtaleBaseChange f).obj (cyclotomicCover hnk) :=
  let := connectedSpace_of_isCurve B X f
  finiteEtaleOverIsoOfFiberEquiv _ (cyclotomicRepresentationFiberEquiv B X f kbar y hnk)
    (cyclotomicRepresentationFiberEquiv_smul B X f kbar y hnk)

/-- **The cover representing `ℱ_{ρ_μ}` is `X ×_k μ_{n,k}`**, as étale `X`-schemes. -/
def cyclotomicRepresentationEtaleIso :
    letI := connectedSpace_of_isCurve B X f
    representationCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n)
        (cyclotomicContinuousModule B X f kbar y n) ≅ rootsOfUnityBaseChangeEtaleObj f hnk :=
  let := connectedSpace_of_isCurve B X f
  MorphismProperty.Over.isoMk (P := @Etale) (Q := ⊤)
    ((MorphismProperty.Over.forget finiteEtale ⊤ X.1 ⋙ CategoryTheory.Over.forget X.1).mapIso
      (cyclotomicRepresentationCoverIso B X f kbar y hnk))
    (MorphismProperty.Over.w (cyclotomicRepresentationCoverIso B X f kbar y hnk).hom)

omit [Smooth f] [GeometricallyConnected f] [Algebra.IsSeparable k kbar] in
/-- The root of unity underlying the point of the fibre of `X ×_k μ_{n,k}` attached to
`ζ ∈ μ_n(k̄)` is the image of `ζ`. -/
theorem rootsOfUnityBaseChangeFiberEquiv_cyclotomicFiberEquiv (ζ : _root_.rootsOfUnity n kbar) :
    rootsOfUnityBaseChangeFiberEquiv f hnk (curveGeometricBasePoint B X f kbar y)
        (cyclotomicFiberEquiv B X f kbar y hnk ζ) =
      geometricPointRootsOfUnityEquiv B X f kbar y n ζ := by
  change rootsOfUnityFiniteEtaleFiberEquiv (Spec (.of k)) n hnk
    ((curveGeometricBasePoint B X f kbar y).map f)
      (finiteEtaleFiberProjection f (curveGeometricBasePoint B X f kbar y) (cyclotomicCover hnk)
        (cyclotomicFiberEquiv B X f kbar y hnk ζ)) = _
  rw [finiteEtaleFiberProjection_cyclotomicFiberEquiv,
    rootsOfUnityFiniteEtaleFiberEquiv_cyclotomicCoverPoint]

omit [IsCurve k f] [Smooth f] [GeometricallyConnected f] [Algebra.IsAlgebraic k kbar]
  [Algebra.IsSeparable k kbar] in
/-- `AlgebraicGeometry.geometricPointRootsOfUnityEquiv` is multiplicative. -/
theorem geometricPointRootsOfUnityEquiv_mul (ζ ξ : _root_.rootsOfUnity n kbar) :
    (geometricPointRootsOfUnityEquiv B X f kbar y n (ζ * ξ)).1 =
      (geometricPointRootsOfUnityEquiv B X f kbar y n ζ).1 *
        (geometricPointRootsOfUnityEquiv B X f kbar y n ξ).1 :=
  map_mul (Units.map (geometricPointResidueRingHom B X f kbar y).toMonoidHom) (ζ : kbarˣ) ξ

/-- **The bijection `ℱ_{ρ_μ}(U) ≃ μ_n(U)`.** A section of `ℱ_{ρ_μ}` over `U` is the restriction of
the tautological section along a unique `t : U ⟶ V` into the representing cover; it is sent to the
restriction of the universal root of unity along `t` followed by `V ≅ X ×_k μ_{n,k}`. -/
def cyclotomicRepresentationSectionEquiv (U : X.1.Etale) :
    letI := connectedSpace_of_isCurve B X f
    ((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
        (cyclotomicContinuousModule B X f kbar y n)).obj.obj (op U) ≃
      ToType ((rootsOfUnitySheaf.{u, 0} X.1 n).obj.obj (op U)) :=
  let := connectedSpace_of_isCurve B X f
  (Equiv.ofBijective _ (bijective_map_representationTautologicalSection B
    (curveGeometricBasePoint B X f kbar y) (ZMod n) (cyclotomicContinuousModule B X f kbar y n)
      U)).symm.trans
    ((cyclotomicRepresentationEtaleIso B X f kbar y hnk).homToEquiv.trans
      (Equiv.ofBijective _
        (isRepresentedBy_rootsOfUnityBaseChangeUniversalSection.{u, 0} f n hnk).map_bijective))

omit [Smooth f] in
/-- The defining property of `AlgebraicGeometry.cyclotomicRepresentationSectionEquiv`. -/
theorem cyclotomicRepresentationSectionEquiv_map {U : X.1.Etale}
    (t : letI := connectedSpace_of_isCurve B X f
      U ⟶ representationCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n)
        (cyclotomicContinuousModule B X f kbar y n)) :
    letI := connectedSpace_of_isCurve B X f
    cyclotomicRepresentationSectionEquiv B X f kbar y hnk U
        (((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n)).obj.map t.op
            (representationTautologicalSection B X _ (ZMod n)
              (cyclotomicContinuousModule B X f kbar y n))) =
      (rootsOfUnitySheaf.{u, 0} X.1 n).obj.map
        (t ≫ (cyclotomicRepresentationEtaleIso B X f kbar y hnk).hom).op
        (rootsOfUnityBaseChangeUniversalSection.{u, 0} f n hnk) := by
  let := connectedSpace_of_isCurve B X f
  have h := (Equiv.ofBijective _ (bijective_map_representationTautologicalSection B
    (curveGeometricBasePoint B X f kbar y) (ZMod n) (cyclotomicContinuousModule B X f kbar y n)
      U)).symm_apply_apply t
  exact congrArg (fun t' ↦ (rootsOfUnitySheaf.{u, 0} X.1 n).obj.map
    (t' ≫ (cyclotomicRepresentationEtaleIso B X f kbar y hnk).hom).op
      (rootsOfUnityBaseChangeUniversalSection.{u, 0} f n hnk)) h

/-- Restricting along `h ≫ t` is restricting along `t`, then along `h`. -/
private theorem map_comp_op_apply {C A : Type*} [Category C] [Category A] {FA : A → A → Type*}
    {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    (F : Cᵒᵖ ⥤ A) {U V W : C} (h : V ⟶ U) (t : U ⟶ W) (s : ToType (F.obj (op W))) :
    F.map (h ≫ t).op s = F.map h.op (F.map t.op s) := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

omit [Smooth f] in
/-- `AlgebraicGeometry.cyclotomicRepresentationSectionEquiv` is natural in `U`. -/
theorem cyclotomicRepresentationSectionEquiv_naturality {U V : X.1.Etale} (h : V ⟶ U)
    (s : letI := connectedSpace_of_isCurve B X f
      ((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
        (cyclotomicContinuousModule B X f kbar y n)).obj.obj (op U)) :
    letI := connectedSpace_of_isCurve B X f
    cyclotomicRepresentationSectionEquiv B X f kbar y hnk V
        (((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n)).obj.map h.op s) =
      (rootsOfUnitySheaf.{u, 0} X.1 n).obj.map h.op
        (cyclotomicRepresentationSectionEquiv B X f kbar y hnk U s) := by
  let := connectedSpace_of_isCurve B X f
  obtain ⟨t, rfl⟩ := (bijective_map_representationTautologicalSection B
    (curveGeometricBasePoint B X f kbar y) (ZMod n) (cyclotomicContinuousModule B X f kbar y n)
      U).2 s
  dsimp only
  rw [← map_comp_op_apply, cyclotomicRepresentationSectionEquiv_map,
    cyclotomicRepresentationSectionEquiv_map, Category.assoc, map_comp_op_apply]

/-- The morphism of representing covers `V_ρ ⟶ V_{ρ'}` attached to a morphism `ρ ⟶ ρ'`, on
Mathlib's small étale site. -/
abbrev representationCoverMap {X : B.Scheme} [ConnectedSpace X.1] (x : GeometricPoint X.1)
    (Λ : Type) [Ring Λ] [Finite Λ]
    {ρ ρ' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (φ : ρ ⟶ ρ') : representationCover B X x Λ ρ ⟶ representationCover B X x Λ ρ' :=
  (SmallEtale.toEtaleSite B X.1 X.2).map ((representationCoverSmall B X x Λ).map φ).hom

omit [Smooth f] in
/-- The geometric fibre of a cover map `V_{ρ₂} ⟶ V_{ρ_μ}`, followed by `V_{ρ_μ} ≅ X ×_k μ_{n,k}`,
read through `AlgebraicGeometry.rootsOfUnityBaseChangeFiberEquiv`: it is the image in
`Γ(Spec Ω, 𝒪)` of the root of unity attached to the fibre point by `ρ₂ ⟶ ρ_μ`. -/
theorem rootsOfUnityBaseChangeFiberEquiv_representationCoverMap
    {ρ₂ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n)
        (EtaleFundamentalGroup X.1 (curveGeometricBasePoint B X f kbar y))}
    (φ : ρ₂ ⟶ cyclotomicContinuousModule B X f kbar y n)
    (p : letI := connectedSpace_of_isCurve B X f
      (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).obj
        (representationFiniteEtaleCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n) ρ₂))
    (q : (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).obj
      ((finiteEtaleBaseChange f).obj (cyclotomicCover hnk)))
    (hq : letI := connectedSpace_of_isCurve B X f
      q.1 = p.1 ≫ (representationCoverMap B (curveGeometricBasePoint B X f kbar y) (ZMod n) φ ≫
        (cyclotomicRepresentationEtaleIso B X f kbar y hnk).hom).left) :
    letI := connectedSpace_of_isCurve B X f
    rootsOfUnityBaseChangeFiberEquiv f hnk (curveGeometricBasePoint B X f kbar y) q =
      geometricPointRootsOfUnityEquiv B X f kbar y n
        (cyclotomicContinuousModuleEquiv B X f kbar y
          (φ.hom.hom.hom.hom.hom (representationFibreEquiv B X
            (curveGeometricBasePoint B X f kbar y) (ZMod n) ρ₂ p))) := by
  let := connectedSpace_of_isCurve B X f
  have h1 : q = (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).map
      (cyclotomicRepresentationCoverIso B X f kbar y hnk).hom
        ((finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).map
          ((representingCover B X).map ((representationSetSheaf B X
            (curveGeometricBasePoint B X f kbar y) (ZMod n)).map φ)) p) :=
    Subtype.ext (hq.trans (Category.assoc _ _ _).symm)
  rw [h1, ← cyclotomicRepresentationFiberRoot_naturality]
  have h2 : (finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).map
      (cyclotomicRepresentationCoverIso B X f kbar y hnk).hom
        ((finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).map
          ((representingCover B X).map ((representationSetSheaf B X
            (curveGeometricBasePoint B X f kbar y) (ZMod n)).map φ)) p) =
      cyclotomicRepresentationFiberEquiv B X f kbar y hnk
        ((finiteEtaleFiberFunctor (curveGeometricBasePoint B X f kbar y)).map
          ((representingCover B X).map ((representationSetSheaf B X
            (curveGeometricBasePoint B X f kbar y) (ZMod n)).map φ)) p) :=
    finiteEtaleOverIsoOfFiberEquiv_hom_apply (curveGeometricBasePoint B X f kbar y)
      (cyclotomicRepresentationFiberEquiv B X f kbar y hnk)
      (cyclotomicRepresentationFiberEquiv_smul B X f kbar y hnk) _
  rw [h2, cyclotomicRepresentationFiberEquiv_apply,
    rootsOfUnityBaseChangeFiberEquiv_cyclotomicFiberEquiv]

omit [Smooth f] in
/-- **Restriction of the universal root of unity along a sum of cover maps.** If
`φ₃ = φ₁ + φ₂ : ρ₂ ⟶ ρ_μ` on underlying modules, then on the cover `V₂` representing `ℱ_{ρ₂}` the
root of unity attached to the cover map of `φ₃`, followed by `V ≅ X ×_k μ_{n,k}`, is the product
of those attached to `φ₁` and `φ₂`. This is checked on the geometric fibre at `x̄`, where it is
the multiplicativity of `μ_n(k̄) → μ_n(Ω)`. -/
theorem rootsOfUnityEtaleBaseChangeHomEquiv_representationCoverMap_of_add
    {ρ₂ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n)
        (EtaleFundamentalGroup X.1 (curveGeometricBasePoint B X f kbar y))}
    (φ₁ φ₂ φ₃ : ρ₂ ⟶ cyclotomicContinuousModule B X f kbar y n)
    (hφ : ∀ m, φ₃.hom.hom.hom.hom.hom m = φ₁.hom.hom.hom.hom.hom m + φ₂.hom.hom.hom.hom.hom m) :
    letI := connectedSpace_of_isCurve B X f
    (rootsOfUnityEtaleBaseChangeHomEquiv f n hnk _
        (representationCoverMap B (curveGeometricBasePoint B X f kbar y) (ZMod n) φ₃ ≫
          (cyclotomicRepresentationEtaleIso B X f kbar y hnk).hom)).1 =
      (rootsOfUnityEtaleBaseChangeHomEquiv f n hnk _
        (representationCoverMap B (curveGeometricBasePoint B X f kbar y) (ZMod n) φ₁ ≫
          (cyclotomicRepresentationEtaleIso B X f kbar y hnk).hom)).1 *
      (rootsOfUnityEtaleBaseChangeHomEquiv f n hnk _
        (representationCoverMap B (curveGeometricBasePoint B X f kbar y) (ZMod n) φ₂ ≫
          (cyclotomicRepresentationEtaleIso B X f kbar y hnk).hom)).1 := by
  let := connectedSpace_of_isCurve B X f
  let x := curveGeometricBasePoint B X f kbar y
  let g := (cyclotomicRepresentationEtaleIso B X f kbar y hnk).hom
  let V₂ := representationCover B X x (ZMod n) ρ₂
  let k₁ := representationCoverMap B x (ZMod n) φ₁ ≫ g
  let k₂ := representationCoverMap B x (ZMod n) φ₂ ≫ g
  let k₃ := representationCoverMap B x (ZMod n) φ₃ ≫ g
  let km : V₂ ⟶ rootsOfUnityBaseChangeEtaleObj f hnk :=
    (rootsOfUnityEtaleBaseChangeHomEquiv f n hnk V₂).symm
      ⟨(rootsOfUnityEtaleBaseChangeHomEquiv f n hnk V₂ k₁).1 *
        (rootsOfUnityEtaleBaseChangeHomEquiv f n hnk V₂ k₂).1, by
        rw [mul_pow, (rootsOfUnityEtaleBaseChangeHomEquiv f n hnk V₂ k₁).2,
          (rootsOfUnityEtaleBaseChangeHomEquiv f n hnk V₂ k₂).2, one_mul]⟩
  suffices hkm : k₃ = km by
    change (rootsOfUnityEtaleBaseChangeHomEquiv f n hnk V₂ k₃).1 = _
    rw [hkm, Equiv.apply_symm_apply]
  refine MorphismProperty.Over.Hom.ext ?_
  let W := (finiteEtaleBaseChange f).obj (cyclotomicCover hnk)
  let V₂' := representationFiniteEtaleCover B X x (ZMod n) ρ₂
  let a : V₂' ⟶ W := MorphismProperty.Over.homMk k₃.left (MorphismProperty.Over.w k₃)
  let b : V₂' ⟶ W := MorphismProperty.Over.homMk km.left (MorphismProperty.Over.w km)
  have hab : a = b := by
    refine finiteEtaleOver_hom_ext_of_finiteEtaleFiber x fun p ↦ ?_
    apply (rootsOfUnityBaseChangeFiberEquiv f hnk x).injective
    refine Subtype.ext ?_
    let q₁ := (finiteEtaleFiberFunctor x).map
      (MorphismProperty.Over.homMk k₁.left (MorphismProperty.Over.w k₁) : V₂' ⟶ W) p
    let q₂ := (finiteEtaleFiberFunctor x).map
      (MorphismProperty.Over.homMk k₂.left (MorphismProperty.Over.w k₂) : V₂' ⟶ W) p
    have e₃ := rootsOfUnityBaseChangeFiberEquiv_representationCoverMap B X f kbar y hnk φ₃ p
      ((finiteEtaleFiberFunctor x).map a p) rfl
    have e₁ := rootsOfUnityBaseChangeFiberEquiv_representationCoverMap B X f kbar y hnk φ₁ p
      q₁ rfl
    have e₂ := rootsOfUnityBaseChangeFiberEquiv_representationCoverMap B X f kbar y hnk φ₂ p
      q₂ rfl
    have m₁ := rootsOfUnityBaseChangeFiberEquiv_eq f hnk x k₁ p.1 p.2 q₁ rfl
    have m₂ := rootsOfUnityBaseChangeFiberEquiv_eq f hnk x k₂ p.1 p.2 q₂ rfl
    have mm := rootsOfUnityBaseChangeFiberEquiv_eq f hnk x km p.1 p.2
      ((finiteEtaleFiberFunctor x).map b p) rfl
    rw [Equiv.apply_symm_apply] at mm
    rw [mm, map_mul, ← m₁, ← m₂, e₁, e₂, e₃, hφ, cyclotomicContinuousModuleEquiv_add,
      geometricPointRootsOfUnityEquiv_mul]
  exact congrArg (fun m ↦ m.left) hab

omit [Smooth f] in
/-- On the cover `V₂` representing `ℱ_{ρ_μ ⊞ ρ_μ}`, the section of `μ_n` attached to the cover
map of `p₁ + p₂` is the sum of those attached to `p₁` and `p₂`. -/
theorem rootsOfUnitySheaf_map_representationCoverMap_biprod :
    letI := connectedSpace_of_isCurve B X f
    (rootsOfUnitySheaf.{u, 0} X.1 n).obj.map
        (representationCoverMap B (curveGeometricBasePoint B X f kbar y) (ZMod n)
          (biprod.fst + biprod.snd : cyclotomicContinuousModule B X f kbar y n ⊞
            cyclotomicContinuousModule B X f kbar y n ⟶ cyclotomicContinuousModule B X f kbar y n) ≫
          (cyclotomicRepresentationEtaleIso B X f kbar y hnk).hom).op
        (rootsOfUnityBaseChangeUniversalSection.{u, 0} f n hnk) =
      (rootsOfUnitySheaf.{u, 0} X.1 n).obj.map
          (representationCoverMap B (curveGeometricBasePoint B X f kbar y) (ZMod n)
            (biprod.fst : cyclotomicContinuousModule B X f kbar y n ⊞
              cyclotomicContinuousModule B X f kbar y n ⟶
                cyclotomicContinuousModule B X f kbar y n) ≫
            (cyclotomicRepresentationEtaleIso B X f kbar y hnk).hom).op
          (rootsOfUnityBaseChangeUniversalSection.{u, 0} f n hnk) +
        (rootsOfUnitySheaf.{u, 0} X.1 n).obj.map
          (representationCoverMap B (curveGeometricBasePoint B X f kbar y) (ZMod n)
            (biprod.snd : cyclotomicContinuousModule B X f kbar y n ⊞
              cyclotomicContinuousModule B X f kbar y n ⟶
                cyclotomicContinuousModule B X f kbar y n) ≫
            (cyclotomicRepresentationEtaleIso B X f kbar y hnk).hom).op
          (rootsOfUnityBaseChangeUniversalSection.{u, 0} f n hnk) := by
  let := connectedSpace_of_isCurve B X f
  refine (rootsOfUnitySection_bijective.{u, 0} X.1 n _).1 (Subtype.ext ?_)
  refine (congrArg Subtype.val
    (rootsOfUnitySection_map_rootsOfUnityBaseChangeUniversalSection f hnk _)).trans ?_
  refine (rootsOfUnityEtaleBaseChangeHomEquiv_representationCoverMap_of_add B X f kbar y hnk
    biprod.fst biprod.snd (biprod.fst + biprod.snd) fun _ ↦ rfl).trans ?_
  refine (congrArg₂ (· * ·)
    (congrArg Subtype.val (rootsOfUnitySection_map_rootsOfUnityBaseChangeUniversalSection f hnk _))
    (congrArg Subtype.val
      (rootsOfUnitySection_map_rootsOfUnityBaseChangeUniversalSection f hnk _))).symm.trans ?_
  exact (rootsOfUnitySection_add X.1 n _ _ _).symm

omit [Smooth f] in
/-- **Two sections of `ℱ_{ρ_μ}` and their sum are restrictions through one cover.** Given `s, t`
over `U`, there is `h : U ⟶ V₂` into the cover representing `ℱ_{ρ_μ ⊞ ρ_μ}` such that `s`, `t` and
`s + t` are the restrictions of the tautological section of `ℱ_{ρ_μ}` along `h` followed by the
cover maps of `p₁`, `p₂` and `p₁ + p₂`: take `h` representing `ℱ(ι₁)(s) + ℱ(ι₂)(t)`, `ℱ` being
additive. -/
theorem exists_representationCoverMap_biprod (U : X.1.Etale)
    (s t : letI := connectedSpace_of_isCurve B X f
      ((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
        (cyclotomicContinuousModule B X f kbar y n)).obj.obj (op U)) :
    letI := connectedSpace_of_isCurve B X f
    ∃ h : U ⟶ representationCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n)
        (cyclotomicContinuousModule B X f kbar y n ⊞ cyclotomicContinuousModule B X f kbar y n),
      s = ((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n)).obj.map
            (h ≫ representationCoverMap B (curveGeometricBasePoint B X f kbar y) (ZMod n)
              biprod.fst).op
            (representationTautologicalSection B X _ (ZMod n)
              (cyclotomicContinuousModule B X f kbar y n)) ∧
      t = ((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n)).obj.map
            (h ≫ representationCoverMap B (curveGeometricBasePoint B X f kbar y) (ZMod n)
              biprod.snd).op
            (representationTautologicalSection B X _ (ZMod n)
              (cyclotomicContinuousModule B X f kbar y n)) ∧
      s + t = ((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n)).obj.map
            (h ≫ representationCoverMap B (curveGeometricBasePoint B X f kbar y) (ZMod n)
              (biprod.fst + biprod.snd)).op
            (representationTautologicalSection B X _ (ZMod n)
              (cyclotomicContinuousModule B X f kbar y n)) := by
  let := connectedSpace_of_isCurve B X f
  let x := curveGeometricBasePoint B X f kbar y
  let ρ := cyclotomicContinuousModule B X f kbar y n
  let Fr := representationSheaf B X x (ZMod n)
  have := preservesFiniteLimits_representationSheaf B X x (ZMod n)
  have : Fr.Additive := Functor.additive_of_preserves_binary_products _
  have hcomp : ∀ {A A' A'' : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n)
      (EtaleFundamentalGroup X.1 x)} (a : A ⟶ A') (b : A' ⟶ A'') (w : (Fr.obj A).obj.obj (op U)),
      (Fr.map b).hom.app (op U) ((Fr.map a).hom.app (op U) w) =
        (Fr.map (a ≫ b)).hom.app (op U) w := by
    intro A A' A'' a b w
    rw [Fr.map_comp]
    rfl
  let z := (Fr.map (biprod.inl : ρ ⟶ ρ ⊞ ρ)).hom.app (op U) s +
    (Fr.map (biprod.inr : ρ ⟶ ρ ⊞ ρ)).hom.app (op U) t
  obtain ⟨h, hh⟩ := (bijective_map_representationTautologicalSection B x (ZMod n) (ρ ⊞ ρ) U).2 z
  have key : ∀ φ : ρ ⊞ ρ ⟶ ρ, (Fr.map φ).hom.app (op U) z =
      (Fr.obj ρ).obj.map (h ≫ representationCoverMap B x (ZMod n) φ).op
        (representationTautologicalSection B X x (ZMod n) ρ) := by
    intro φ
    rw [← hh]
    refine (ConcreteCategory.congr_hom ((Fr.map φ).hom.naturality h.op)
      (representationTautologicalSection B X x (ZMod n) (ρ ⊞ ρ))).trans ?_
    change (Fr.obj ρ).obj.map h.op ((Fr.map φ).hom.app _
      (representationTautologicalSection B X x (ZMod n) (ρ ⊞ ρ))) = _
    rw [representationTautologicalSection_naturality, map_comp_op_apply]
  have hz : (Fr.map (biprod.fst : ρ ⊞ ρ ⟶ ρ)).hom.app (op U) z = s ∧
      (Fr.map (biprod.snd : ρ ⊞ ρ ⟶ ρ)).hom.app (op U) z = t := by
    simp only [z, map_add, hcomp]
    simp
  refine ⟨h, hz.1.symm.trans (key _), hz.2.symm.trans (key _), Eq.trans ?_ (key _)⟩
  rw [Fr.map_add]
  exact (congrArg₂ (· + ·) hz.1 hz.2).symm

omit [Smooth f] in
/-- **`AlgebraicGeometry.cyclotomicRepresentationSectionEquiv` is additive**, by
`AlgebraicGeometry.exists_representationCoverMap_biprod` and
`AlgebraicGeometry.rootsOfUnitySheaf_map_representationCoverMap_biprod`. -/
theorem cyclotomicRepresentationSectionEquiv_add (U : X.1.Etale)
    (s t : letI := connectedSpace_of_isCurve B X f
      ((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
        (cyclotomicContinuousModule B X f kbar y n)).obj.obj (op U)) :
    cyclotomicRepresentationSectionEquiv B X f kbar y hnk U (s + t) =
      cyclotomicRepresentationSectionEquiv B X f kbar y hnk U s +
        cyclotomicRepresentationSectionEquiv B X f kbar y hnk U t := by
  let := connectedSpace_of_isCurve B X f
  obtain ⟨h, hs, ht, hst⟩ := exists_representationCoverMap_biprod B X f kbar y U s t
  rw [hst, hs, ht, cyclotomicRepresentationSectionEquiv_map,
    cyclotomicRepresentationSectionEquiv_map, cyclotomicRepresentationSectionEquiv_map,
    Category.assoc, Category.assoc, Category.assoc, map_comp_op_apply _ h, map_comp_op_apply _ h,
    map_comp_op_apply _ h, rootsOfUnitySheaf_map_representationCoverMap_biprod, map_add]

end Comparison

section Main

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n] (hn : IsUnit (n : k))

/-- **`ℱ_{ρ_μ} = μ_n`.** For a geometrically connected smooth curve `X` over `k`, an algebraic
closure `k̄` of `k` separable over `k`, a geometric point `η̄` of `X_k̄` with image `x̄` in `X`,
and an integer `n` invertible in `k`, the abelian sheaf underlying the sheaf `ℱ_{ρ_μ}` of
Tag 0DV5 (3) attached to the cyclotomic representation `ρ_μ = μ_n(k̄)` of `π₁(X, x̄)`
(`AlgebraicGeometry.cyclotomicContinuousModule`) is the sheaf `μ_n` of `n`-th roots of unity on
`X_étale`, the kernel of the `n`-th power map on `𝐆_m` (`Stacks.Kummer.rootsOfUnitySheaf`).

On sections over `U` it sends the restriction of the tautological section of `ℱ_{ρ_μ}` along
`t : U ⟶ V`, `V` the representing cover, to the root of unity on `U` given by
`U ⟶ V ≅ X ×_k μ_{n,k}` (`AlgebraicGeometry.cyclotomicRepresentationSheafIso_hom_app_map`); the
isomorphism `V ≅ X ×_k μ_{n,k}` is the one inducing, on geometric fibres at `x̄`, the identity of
`μ_n(k̄)` read through `AlgebraicGeometry.representationFibreEquiv` and
`AlgebraicGeometry.cyclotomicFiberEquiv` (`AlgebraicGeometry.cyclotomicRepresentationCoverIso`). -/
def cyclotomicRepresentationSheafIso :
    letI := connectedSpace_of_isCurve B X f
    (Stacks.EtaleCohomology.etaleModuleUnderlyingAbelian X.1 (ZMod n)).obj
        ((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n)) ≅
      rootsOfUnitySheaf.{u, 0} X.1 n :=
  let := connectedSpace_of_isCurve B X f
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ AddEquiv.toAddCommGrpIso
    { toEquiv := cyclotomicRepresentationSectionEquiv B X f kbar y
        (isUnit_natCast_ΓSpec_of_isUnit n hn) U.unop
      map_add' := cyclotomicRepresentationSectionEquiv_add B X f kbar y
        (isUnit_natCast_ΓSpec_of_isUnit n hn) U.unop })
    (fun {U V} h ↦ by
      ext s
      exact cyclotomicRepresentationSectionEquiv_naturality B X f kbar y
        (isUnit_natCast_ΓSpec_of_isUnit n hn) h.unop s))

omit [Smooth f] in
/-- **`AlgebraicGeometry.cyclotomicRepresentationSheafIso` on sections**: the restriction of the
tautological section of `ℱ_{ρ_μ}` along `t : U ⟶ V` goes to the restriction of the universal
root of unity along `U ⟶ V ≅ X ×_k μ_{n,k}`. -/
theorem cyclotomicRepresentationSheafIso_hom_app_map {U : X.1.Etale}
    (t : letI := connectedSpace_of_isCurve B X f
      U ⟶ representationCover B X (curveGeometricBasePoint B X f kbar y) (ZMod n)
        (cyclotomicContinuousModule B X f kbar y n)) :
    letI := connectedSpace_of_isCurve B X f
    (cyclotomicRepresentationSheafIso B X f kbar y n hn).hom.hom.app (op U)
        (((representationSheaf B X (curveGeometricBasePoint B X f kbar y) (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n)).obj.map t.op
            (representationTautologicalSection B X _ (ZMod n)
              (cyclotomicContinuousModule B X f kbar y n))) =
      (rootsOfUnitySheaf.{u, 0} X.1 n).obj.map
        (t ≫ (cyclotomicRepresentationEtaleIso B X f kbar y
          (isUnit_natCast_ΓSpec_of_isUnit n hn)).hom).op
        (rootsOfUnityBaseChangeUniversalSection.{u, 0} f n (isUnit_natCast_ΓSpec_of_isUnit n hn)) :=
  cyclotomicRepresentationSectionEquiv_map B X f kbar y (isUnit_natCast_ΓSpec_of_isUnit n hn) t

end Main

end AlgebraicGeometry

end
