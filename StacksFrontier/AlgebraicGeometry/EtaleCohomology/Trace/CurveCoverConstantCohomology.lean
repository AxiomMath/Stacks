module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactificationIntegralComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantModuleCohomology
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# `H²(C, j_! φ_* E_V) = E` for a connected finite étale cover of an open of a curve

Let `C` be a smooth proper curve over an algebraically closed field `K`, `j : U ⟶ C` an open
immersion with finite complement, `φ : V ⟶ U` a finite étale morphism with `V` connected and `Λ` a
finite ring whose order is invertible in `K`. For a finite `Λ`-module `E` this file constructs a
`Λ`-linear isomorphism
`H²(C, j_!(φ_* E_V)) ≃ E`,
natural in `E`. Let `V̄` be the smooth projective compactification of the cover, with the finite
`φ̄ : V̄ ⟶ C` extending `φ` and `V = V̄ ×_C U` (`AlgebraicGeometry.CoverCompactification`). Then
`j_! φ_* = φ̄_* j_{V!}`, since extension by zero commutes with integral direct images, and
`H²(C, φ̄_* G) = H²(V̄, G)` because `φ̄_*` is exact. Finally `H²(V̄, j_{V!} E_V) = E` by the trace
of the curve `V̄` (`Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace`).

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroDirectImageIntegralIso` — `j_! ∘ f_* ≅ f̄_* ∘ j'_!` for a
  cartesian square with `j`, `j'` open immersions and `f̄` integral.
* `Stacks.EtaleCohomology.curveCoverCompactification` — the compactification of the cover.
* `Stacks.EtaleCohomology.curveExtensionByZeroDirectImageConstantTrace` —
  `H²(C, j_!(φ_* E_V)) ≃ₗ[Λ] E`.

## Main results

* `AlgebraicGeometry.isCurve_comp_of_isOpenImmersion_of_nonempty` — a nonempty open subscheme of
  a curve is a curve.
* `Stacks.EtaleCohomology.curveExtensionByZeroDirectImageConstantTrace_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **A nonempty open subscheme of a curve is a curve**: it is integral, and it has the dimension
of the curve because a variety has the dimension of each of its nonempty opens. -/
theorem isCurve_comp_of_isOpenImmersion_of_nonempty (k : Type u) [Field k] {U C : Scheme.{u}}
    (q : C ⟶ Spec (.of k)) [IsCurve k q] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U] :
    IsCurve k (j ≫ q) := by
  have : IsIntegral C := IsCurve.toIsVariety.toIsIntegral (k := k) (f := q)
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian C := ⟨⟩
  have hdim : topologicalKrullDim U = 1 := by
    rw [← IsCurve.topologicalKrullDim_eq_one q,
      topologicalKrullDim_eq_of_isOpen k C q (Set.range j.base) j.isOpenEmbedding.isOpen_range
        (Set.range_nonempty _)]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (j.isOpenEmbedding.toIsEmbedding.toHomeomorph).isHomeomorph
  have : IsIntegral ((𝟭 Scheme).obj U) := ‹IsIntegral U›
  exact (isCurve_iff k _).2 ⟨IsVariety.mk, hdim⟩

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/- The cohomology groups consumed here (`Stacks.EtaleCohomology.integralDirectImageCohomologyIso`,
`Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace`) are built in the standard model of the
derived category, so the statements of this file are read in that model too. -/
attribute [local instance] HasDerivedCategory.standard etaleModulesEnoughInjectivesZero

section Cartesian

variable (Λ : Type) [Ring Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [IsOpenImmersion j]
  (j' : V ⟶ Vb) [IsOpenImmersion j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]
  (sq : IsPullback f j' j fb)

omit [IsOpenImmersion j] [IsOpenImmersion j'] [IsIntegralHom fb] in
include sq in
/-- The image of `j'` is the preimage under `f̄` of the image of `j`, for a cartesian square
`f ≫ j = j' ≫ f̄`. -/
theorem range_eq_preimage_range_of_isPullback_of_isOpenImmersion :
    Set.range j'.base = fb.base ⁻¹' Set.range j.base := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨f a, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sq.w]
  · rintro ⟨b, hb⟩
    obtain ⟨z, hz⟩ : x ∈ Set.range (pullback.fst fb j).base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨b, hb⟩
    refine ⟨sq.flip.isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz]

/-- **`j_! ∘ f_* ≅ f̄_* ∘ j'_!`**, naturally, for a cartesian square `f ≫ j = j' ≫ f̄` with `j`,
`j'` open immersions and `f̄` integral: extension by zero commutes with the integral direct image,
the closed complements being the reduced complement of `j` and its preimage. -/
def extensionByZeroDirectImageIntegralIso :
    etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleExtensionByZero.{u, 0} Λ j ≅
      etaleModuleExtensionByZero.{u, 0} Λ j' ⋙ etaleModuleDirectImage.{u, 0} Λ fb :=
  let ι := (Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subschemeι
  haveI : ∀ M, IsIso ((extensionByZeroIntegralDirectImageNatTrans Λ j j' f fb sq).app M) :=
    fun M => by
    rw [extensionByZeroIntegralDirectImageNatTrans_app]
    refine isIso_extensionByZeroIntegralDirectImageMap Λ j j' f fb sq ι
      (by rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_mk,
        compl_compl]) (pullback.snd ι fb) ?_
      (pullback.fst ι fb) (IsPullback.of_hasPullback ι fb) M
    rw [Scheme.Pullback.range_snd, Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_mk,
        Set.preimage_compl, compl_compl]
    exact range_eq_preimage_range_of_isPullback_of_isOpenImmersion j j' f fb sq
  haveI := NatIso.isIso_of_isIso_app (extensionByZeroIntegralDirectImageNatTrans Λ j j' f fb sq)
  asIso (extensionByZeroIntegralDirectImageNatTrans Λ j j' f fb sq)

end Cartesian

/-- The linear equivalence of an isomorphism of modules applied to an element, written through
the underlying linear map of the isomorphism. -/
lemma moduleCatIso_toLinearEquiv_apply_eq {R : Type*} [Ring R] {M N : ModuleCat R} (e : M ≅ N)
    (x : M) : e.toLinearEquiv x = e.hom.hom x :=
  rfl

/-- Two commutative squares compose: if `e' ∘ a = b ∘ e` and `t' ∘ b = g ∘ t`, then
`(t' ∘ e') ∘ a = g ∘ (t ∘ e)`, read on elements. -/
lemma linearEquiv_trans_apply_of_squares {R : Type*} [Ring R] {A A' B B' E E' : Type*}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B'] [AddCommGroup E]
    [AddCommGroup E'] [Module R A] [Module R A'] [Module R B] [Module R B'] [Module R E]
    [Module R E'] (e : A ≃ₗ[R] B) (e' : A' ≃ₗ[R] B') (t : B ≃ₗ[R] E) (t' : B' ≃ₗ[R] E')
    (a : A →ₗ[R] A') (b : B →ₗ[R] B') (g : E →ₗ[R] E') (h₁ : ∀ x, e' (a x) = b (e x))
    (h₂ : ∀ y, t' (b y) = g (t y)) (x : A) :
    (e'.trans t') (a x) = g ((e.trans t) x) := by
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h₁, h₂]

section Trace

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] (Λ : Type) [Ring Λ] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  {U : Scheme.{u}} (jC : U ⟶ C) [IsOpenImmersion jC]
  {V : Scheme.{u}} (φ : V ⟶ U) [IsFinite φ] [Etale φ] [ConnectedSpace V]

/-- **The smooth projective compactification of the cover `φ : V ⟶ U` over `C`**: a smooth proper
curve `V̄` over `K` with an open immersion `V ⟶ V̄` of finite complement and a finite
`φ̄ : V̄ ⟶ C` extending `φ`, with `V = V̄ ×_C U`. The field `K` is perfect, being algebraically
closed, and `U` is a smooth curve, being a nonempty open of `C`. -/
def curveCoverCompactification : CoverCompactification K q jC φ :=
  haveI : Nonempty V := ConnectedSpace.toNonempty
  haveI : Nonempty U := ⟨φ.base (Classical.arbitrary V)⟩
  haveI := isCurve_comp_of_isOpenImmersion_of_nonempty K q jC
  (nonempty_coverCompactification K (jC ≫ q) q jC rfl φ).some

/-- **`H²(C, j_!(φ_* G)) ≅ H²(V̄, j_{V!} G)`** for a sheaf `G` of `Λ`-modules on `V`: extension by
zero commutes with the finite direct image `φ̄_*`, which is exact. -/
def curveCoverExtensionByZeroCohomologyIso (G : EtaleModules.{u, 0} Λ V) :
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj ((etaleModuleDirectImage.{u, 0} Λ φ).obj G)) ≅
      ((etaleModuleGlobalSections.{u, 0} Λ (curveCoverCompactification q jC φ).Vb).rightDerivedPlus
          ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ (curveCoverCompactification q jC φ).j).obj G) :=
  ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).mapIso
      ((extensionByZeroDirectImageIntegralIso Λ jC (curveCoverCompactification q jC φ).j φ
        (curveCoverCompactification q jC φ).fb
        (curveCoverCompactification q jC φ).isPullback.flip).app G) ≪≫
    integralDirectImageCohomologyIso Λ (curveCoverCompactification q jC φ).fb _ ((2 : ℕ) : ℤ)

omit [Fintype Λ] in
/-- `Stacks.EtaleCohomology.curveCoverExtensionByZeroCohomologyIso` is natural in the sheaf. -/
theorem curveCoverExtensionByZeroCohomologyIso_hom_naturality {G G' : EtaleModules.{u, 0} Λ V}
    (m : G ⟶ G') :
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).map ((etaleModuleDirectImage.{u, 0} Λ φ).map m)) ≫
        (curveCoverExtensionByZeroCohomologyIso q Λ jC φ G').hom =
      (curveCoverExtensionByZeroCohomologyIso q Λ jC φ G).hom ≫
        ((etaleModuleGlobalSections.{u, 0} Λ
          (curveCoverCompactification q jC φ).Vb).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ (curveCoverCompactification q jC φ).j).map m) := by
  have h1 := congrArg ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
    ((extensionByZeroDirectImageIntegralIso Λ jC (curveCoverCompactification q jC φ).j φ
      (curveCoverCompactification q jC φ).fb
      (curveCoverCompactification q jC φ).isPullback.flip).hom.naturality m)
  rw [Functor.map_comp, Functor.map_comp] at h1
  dsimp only [Functor.comp_map] at h1
  simp only [curveCoverExtensionByZeroCohomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  rw [← Category.assoc, h1, Category.assoc,
    integralDirectImageCohomologyIso_hom_naturality Λ (curveCoverCompactification q jC φ).fb
      ((etaleModuleExtensionByZero.{u, 0} Λ (curveCoverCompactification q jC φ).j).map m)
      ((2 : ℕ) : ℤ), Category.assoc]

/-- **`H²(C, j_!(φ_* E_V)) ≃ E`** for a connected finite étale cover `φ : V ⟶ U` of an open
`j : U ⟶ C` with finite complement of a smooth proper curve `C` over an algebraically closed
field, and a finite module `E` over a finite ring `Λ` of order invertible in the field: through
the compactification `V̄` of the cover, `j_! φ_* = φ̄_* j_{V!}` and `H²(C, φ̄_* -) = H²(V̄, -)`,
and `H²(V̄, j_{V!} E_V) = E` by the trace (depending on the primitive root `ζ`). -/
def curveExtensionByZeroDirectImageConstantTrace (E : ModuleCat.{u + 1} Λ) [Finite E] :
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((etaleModuleDirectImage.{u, 0} Λ φ).obj
            ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) ≃ₗ[Λ] E :=
  (curveCoverExtensionByZeroCohomologyIso q Λ jC φ _).toLinearEquiv.trans
    (curveExtensionByZeroConstantTrace (curveCoverCompactification q jC φ).q Λ hn hζ
      (curveCoverCompactification q jC φ).j (curveCoverCompactification q jC φ).finite_compl E)

/-- `Stacks.EtaleCohomology.curveExtensionByZeroDirectImageConstantTrace` is the composite of
`Stacks.EtaleCohomology.curveCoverExtensionByZeroCohomologyIso` with the trace
`Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace` of the compactification. -/
lemma curveExtensionByZeroDirectImageConstantTrace_eq (E : ModuleCat.{u + 1} Λ) [Finite E] :
    curveExtensionByZeroDirectImageConstantTrace q Λ hn hζ jC φ E =
      (curveCoverExtensionByZeroCohomologyIso q Λ jC φ
          ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)).toLinearEquiv.trans
        (curveExtensionByZeroConstantTrace (curveCoverCompactification q jC φ).q Λ hn hζ
          (curveCoverCompactification q jC φ).j (curveCoverCompactification q jC φ).finite_compl
          E) :=
  rfl

/-- **`H²(C, j_!(φ_* E_V)) ≃ E` is natural in `E`.** -/
theorem curveExtensionByZeroDirectImageConstantTrace_naturality {E E' : ModuleCat.{u + 1} Λ}
    [Finite E] [Finite E'] (g : E ⟶ E')
    (x : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((etaleModuleDirectImage.{u, 0} Λ φ).obj
            ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)))) :
    curveExtensionByZeroDirectImageConstantTrace q Λ hn hζ jC φ E'
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map ((etaleModuleDirectImage.{u, 0} Λ φ).map
            ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g)))).hom x) =
      g (curveExtensionByZeroDirectImageConstantTrace q Λ hn hζ jC φ E x) := by
  have hS : ∀ y, (curveCoverExtensionByZeroCohomologyIso q Λ jC φ _).toLinearEquiv
      ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map ((etaleModuleDirectImage.{u, 0} Λ φ).map
            ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g)))).hom y) =
      (((etaleModuleGlobalSections.{u, 0} Λ (curveCoverCompactification q jC φ).Vb).rightDerivedPlus
          ((2 : ℕ) : ℤ)).map ((etaleModuleExtensionByZero.{u, 0} Λ
            (curveCoverCompactification q jC φ).j).map
              ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g))).hom
        ((curveCoverExtensionByZeroCohomologyIso q Λ jC φ _).toLinearEquiv y) := fun y ↦ by
    have h := congrArg (fun t ↦ t.hom y)
      (curveCoverExtensionByZeroCohomologyIso_hom_naturality q Λ jC φ
        ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map g))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  rw [curveExtensionByZeroDirectImageConstantTrace_eq,
    curveExtensionByZeroDirectImageConstantTrace_eq]
  exact linearEquiv_trans_apply_of_squares
    (curveCoverExtensionByZeroCohomologyIso q Λ jC φ _).toLinearEquiv
    (curveCoverExtensionByZeroCohomologyIso q Λ jC φ _).toLinearEquiv
    (curveExtensionByZeroConstantTrace (curveCoverCompactification q jC φ).q Λ hn hζ
      (curveCoverCompactification q jC φ).j (curveCoverCompactification q jC φ).finite_compl E)
    (curveExtensionByZeroConstantTrace (curveCoverCompactification q jC φ).q Λ hn hζ
      (curveCoverCompactification q jC φ).j (curveCoverCompactification q jC φ).finite_compl E')
    _ _ g.hom hS (curveExtensionByZeroConstantTrace_naturality
      (curveCoverCompactification q jC φ).q Λ hn hζ (curveCoverCompactification q jC φ).j
      (curveCoverCompactification q jC φ).finite_compl g) x

end Trace

end Stacks.EtaleCohomology

end
