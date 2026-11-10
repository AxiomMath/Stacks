module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedKernel
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleBaseChangeNaturality

/-!
# The affine sections of an associated module and base change

Let `S` be a scheme, `B` a chosen big site over `S`, and `Spec A ⟶ S` an affine scheme *of the
site*. For a sheaf of modules `𝓕` on the site, `F_{𝓕, A}` is the module-valued functor
`C ↦ 𝓕(Spec C)` on the `A`-algebras of the site (`Stacks.Adequate.affineSectionFunctor`).
Because `Spec A` is itself an object of the site there is a canonical comparison

`C ⊗_A 𝓕(Spec A) ⟶ 𝓕(Spec C)`,  `c ⊗ m ↦ c · m|_{Spec C}`,

natural in `C` *and* in `𝓕`. This file builds it, and proves separately that the corresponding
comparison for an associated module `𝓖ᵃ` is bijective, which is the clause of Descent,
Proposition 03DX computing the sections of `𝓖ᵃ` over an affine as a base change
(`Stacks.Sites.affineAssociatedBaseChangeIso`).

## Main definitions

* `Stacks.Adequate.tensorBaseRingHom` transports a tensor product along compatible isomorphisms
  of the base ring and of the left factor. It is what converts a base change along
  `Γ(Spec A, 𝒪) ⟶ Γ(Spec C, 𝒪)` into one along `A ⟶ C`; the two module structures involved are
  explicit arguments, because both are in scope at the intended application.
* `Stacks.Adequate.baseSiteAlgebra` is `A` itself as an object of the category of `A`-algebras
  of the site. This is the only use of the hypothesis `schemeSizeBelow B.cutoff (Spec A)`, and
  it is what makes the comparison exist at all.
* `Stacks.Adequate.affineBaseSections` is the `A`-module `𝓕(Spec A)` of sections over the base
  affine, and `Stacks.Adequate.affineBaseSectionsMap` the `A`-module map which a map of sheaves
  of modules induces on it.
* `Stacks.Adequate.affineSectionsCompare` is the comparison `C ⊗_A 𝓕(Spec A) ⟶ F_{𝓕, A}` as a
  morphism of module-valued functors.

## Main results

* `Stacks.Adequate.affineSectionsCompare_naturality` — **the comparison is natural in the sheaf
  of modules.** This costs nothing: the comparison is `c ⊗ m ↦ c · m|` for every sheaf, and a
  map of sheaves of modules is linear and commutes with restriction. It is the step which turns
  a map `𝓖ᵃ ⟶ 𝓗ᵃ` into a map of module extensions, with the module map the component of the
  given map over `Spec A`.
* `Stacks.Adequate.exists_bijective_sectionsBaseChange` — **the affine base change of Descent,
  Proposition 03DX in a form that mentions no site.** For a morphism `g : W ⟶ W₀` of schemes
  over `S` with affine total spaces, and any identification of a ring `R` with `Γ(W₀, 𝒪)` and of
  an `R`-module `Cc` with `Γ(W, 𝒪)`, the map `c ⊗ m ↦ c · m|_W` from `Cc ⊗_R Γ(W₀.hom⁺𝓖, 𝒪)` to
  `Γ(W.hom⁺𝓖, 𝒪)` is bijective. This is `Stacks.Sites.affineBaseChangeIsoOfEq` composed with
  `Stacks.Sites.pullbackSectionsComparison`, with the base ring moved by
  `Stacks.Adequate.tensorBaseRingHom`.
* `Stacks.Adequate.baseChangeRingMap_gammaSpec` — the coherence between the two base changes:
  the ring map the affine base change is taken along agrees, through `Γ(Spec R, 𝒪) ≅ R`, with
  the structure map of the algebra.
* `Stacks.Adequate.associatedModule_val_map_eq` — the restriction maps of an associated module
  are the pullback maps on sections of [Stacks, Tag 03DS].
* `Stacks.Adequate.affineBaseRestrict_val` — restriction from the base affine is the
  restriction map of the sheaf, stated once and generically in the sheaf.
* `Stacks.Adequate.associatedModule_val_map_affineBase` — the other cheap half: for an
  associated module, the restriction maps out of the base affine are the pullback maps on
  sections, with the section in the affine-section spelling.
* `Stacks.Adequate.affineBaseRestrict_eq_of_val_map` — the bridge which lets those two halves
  compose, with both the sheaf and the morphism of the site left variable.
* `Stacks.Adequate.affineBaseRestrict_associatedModule` — their composition: restriction of a
  section of `𝓖ᵃ` from the base affine is the pullback map on sections.
* `Stacks.Adequate.affineSections_smul_eq` — the two scalar actions on the affine sections agree
  at a general algebra of the site.
* `Stacks.Adequate.bijective_affineSectionsCompareFun` — **the comparison is bijective at every
  algebra of the site**, because it agrees on generators with the affine base change.
* `Stacks.Adequate.isIso_affineSectionsCompare` — hence the comparison is an isomorphism of
  module-valued functors: the affine sections of an associated module *are* a module extension.
* `Stacks.Adequate.affineAssociatedSections` — **`Stacks.Adequate.AffineAssociatedSections`,
  discharged.**
* `Stacks.Adequate.isAdequate_of_isAssociatedKernel` and
  `Stacks.Adequate.isAdequate_of_coveringAssociatedKernel` — consequently [Stacks, Tag 06VK]'s
  implications to adequacy, from a kernel presentation and from a covering by such, each with no
  identification assumed.

## Implementation notes

`Stacks.Adequate.AffineAssociatedSections` **is** proved here, as
`Stacks.Adequate.affineAssociatedSections`. The one identification which used to block it is
`Stacks.Adequate.affineBaseRestrict_associatedModule`, and what it cost is worth recording,
because the same shape recurs throughout this file.

`PresheafOfModules.map` lands in `(ModuleCat.restrictScalars φ).obj (P.obj Y)`, and the two
spellings of a restricted section carry *different* ring presheaves: the pushforward's
`AdequateFunctor.algebraRingDiagramOn` on one side — in fact two such layers —
`B.structureSheaf` on the other. Congruence on `ModuleCat.restrictScalars` therefore fails, and
the unifier descends through `PresheafOfModules.obj` into `Stacks.Sites.associatedPresheaf`.
Mathlib's `ModuleCat.restrictScalarsCongr` does not help: it compares restriction along two ring
maps between the *same* pair of rings.

Every ingredient is cheap and every direct composition is not. Each
half alone — `Stacks.Adequate.affineBaseRestrict_val`,
`Stacks.Adequate.associatedModule_val_map_eq` — is cheap even at a specific sheaf and a specific
morphism; so is the target statement; so is each atomic conversion of carriers. But `Eq.trans`,
`exact`, `rw` of the element-level lemma, `simp only`, a type ascription and a plain `rfl` all
fail at `isDefEq` or in the kernel. The fix is therefore not a tactic but a shape, and three
rules govern the whole file:

* **Keep the sheaf and the morphism of the site variable through every expensive position.**
  `Stacks.Adequate.affineBaseRestrict_eq_of_val_map` performs the type identification once, where
  it is a millisecond `rfl`; its consumer generalises the structure morphism with
  `obtain ⟨k, hk⟩ : ∃ k, _ = k := ⟨_, rfl⟩`, works at that variable `k`, and substitutes back
  only after the statement is closed.
* **Spell `B.toOver.map _` out rather than using the `Stacks.Adequate.overMapOfAlg`
  abbreviation.** Unfolding it is itself part of the unification being avoided: the same proof
  with the abbreviation in the goal exhausts the kernel, and with the morphism written out it
  checks in seconds. This is why the statements below prefer the long form.
* **Cross between two spellings once, at the top level, never inside an induction.**
  `Stacks.Adequate.exists_bijective_affineSectionsCompare` exists only to restate
  `Stacks.Adequate.exists_bijective_sectionsBaseChange` in the affine-section spelling; done once
  it is free, while an induction over the tensor product that crosses the two spellings at every
  step is over budget.

`Stacks.Adequate.exists_bijective_sectionsBaseChange` is stated with the morphism of `Over S`
abstract rather than at `Stacks.Adequate.overMapOfAlg` for the same family of reasons, and its
remaining hypotheses — `Stacks.Adequate.baseChangeRingMap_gammaSpec`,
`Stacks.Adequate.assocBaseChangeFactor_smul_eq` and
`Stacks.Adequate.affineBaseSections_smul_eq` — are exactly the arguments it takes.

The sections over the base affine carry two actions — the base ring `A` acts through
`Γ(Spec A, 𝒪) ≅ A`, and `Γ(Spec A, 𝒪)` acts directly — and the affine base change uses the
second while the module extension uses the first. They differ by restriction of scalars, so the
transport takes both module structures as explicit arguments: with both in scope the `•`
notation has two resolutions and the statements would be about the wrong one.

Lemmas about the affine-section functor name the presheaf of modules explicitly rather than
leaving it to be inferred. The sections over the base affine are given the type `ModuleCat.{u} A`,
whose ring instance reaches `A` through `CommRingCat`, while the affine-section functor's own
values are modules over the ring of the algebra diagram; the two are definitionally equal, but
inferring the presheaf from an element of the first spelling is a higher-order unification that
does not terminate in reasonable time.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite
open scoped TensorProduct ChangeOfRings

universe w w' u

namespace Stacks.Adequate

/-! ### Transport of a tensor product along isomorphisms of the base and the left factor -/

section TensorTransport

variable {R R' Cc Cc' Mm : Type u} [CommRing R] [CommRing R']
  [AddCommGroup Cc] [AddCommGroup Cc'] [AddCommGroup Mm]
  (iC : Module R Cc) (iC' : Module R' Cc') (iM : Module R Mm) (iM' : Module R' Mm)
  (e : R ≃+* R') (eC : Cc ≃+ Cc')

/-- The additive map `Cc ⊗[R] Mm →+ Cc' ⊗[R'] Mm` sending `c ⊗ₜ m` to `eC c ⊗ₜ m`, induced by a
ring isomorphism `e : R ≃+* R'` and an additive isomorphism `eC : Cc ≃+ Cc'` compatible with the
scalar actions. -/
noncomputable def tensorBaseRingHom
    (hC : ∀ (r : R) (c : Cc),
      eC (@HSMul.hSMul R Cc Cc _ r c) = @HSMul.hSMul R' Cc' Cc' _ (e r) (eC c))
    (hM : ∀ (r : R) (m : Mm),
      @HSMul.hSMul R Mm Mm _ r m = @HSMul.hSMul R' Mm Mm _ (e r) m) :
    @TensorProduct R _ Cc Mm _ _ iC iM →+ @TensorProduct R' _ Cc' Mm _ _ iC' iM' := by
  letI := iC; letI := iC'; letI := iM; letI := iM'
  refine TensorProduct.liftAddHom
    { toFun := fun c =>
        { toFun := fun m => eC c ⊗ₜ[R'] m
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun x y => TensorProduct.tmul_add _ x y }
      map_zero' := AddMonoidHom.ext fun m => by
        simp only [map_zero]
        exact TensorProduct.zero_tmul _ _
      map_add' := fun c d => AddMonoidHom.ext fun m => by
        simp only [map_add]
        exact TensorProduct.add_tmul _ _ _ }
    (fun r c m => ?_)
  change eC (r • c) ⊗ₜ[R'] m = eC c ⊗ₜ[R'] (r • m)
  rw [hC, hM]
  exact TensorProduct.smul_tmul _ _ _

/-- `tensorBaseRingHom` sends `c ⊗ₜ m` to `eC c ⊗ₜ m`. -/
theorem tensorBaseRingHom_tmul
    (hC : ∀ (r : R) (c : Cc),
      eC (@HSMul.hSMul R Cc Cc _ r c) = @HSMul.hSMul R' Cc' Cc' _ (e r) (eC c))
    (hM : ∀ (r : R) (m : Mm),
      @HSMul.hSMul R Mm Mm _ r m = @HSMul.hSMul R' Mm Mm _ (e r) m)
    (c : Cc) (m : Mm) :
    letI := iC; letI := iC'; letI := iM; letI := iM'
    tensorBaseRingHom iC iC' iM iM' e eC hC hM (c ⊗ₜ[R] m) = eC c ⊗ₜ[R'] m := rfl

/-- If `eC` intertwines the `R`-action with the `R'`-action along `e`, then `eC.symm`
intertwines the `R'`-action with the `R`-action along `e.symm`. -/
theorem tensorBaseRing_hC_symm
    (hC : ∀ (r : R) (c : Cc),
      eC (@HSMul.hSMul R Cc Cc _ r c) = @HSMul.hSMul R' Cc' Cc' _ (e r) (eC c)) :
    ∀ (r' : R') (c' : Cc'), eC.symm (@HSMul.hSMul R' Cc' Cc' _ r' c') =
      @HSMul.hSMul R Cc Cc _ (e.symm r') (eC.symm c') := by
  let _ := iC; let _ := iC'
  intro r' c'
  refine eC.injective ?_
  rw [eC.apply_symm_apply, hC, eC.apply_symm_apply, e.apply_symm_apply]

/-- If the `R`-action on `Mm` agrees with the `R'`-action along `e`, then the `R'`-action agrees
with the `R`-action along `e.symm`. -/
theorem tensorBaseRing_hM_symm
    (hM : ∀ (r : R) (m : Mm),
      @HSMul.hSMul R Mm Mm _ r m = @HSMul.hSMul R' Mm Mm _ (e r) m) :
    ∀ (r' : R') (m : Mm), @HSMul.hSMul R' Mm Mm _ r' m =
      @HSMul.hSMul R Mm Mm _ (e.symm r') m := by
  let _ := iM; let _ := iM'
  intro r' m
  rw [hM, e.apply_symm_apply]

/-- The map `tensorBaseRingHom` is bijective. -/
theorem bijective_tensorBaseRingHom
    (hC : ∀ (r : R) (c : Cc),
      eC (@HSMul.hSMul R Cc Cc _ r c) = @HSMul.hSMul R' Cc' Cc' _ (e r) (eC c))
    (hM : ∀ (r : R) (m : Mm),
      @HSMul.hSMul R Mm Mm _ r m = @HSMul.hSMul R' Mm Mm _ (e r) m) :
    Function.Bijective (tensorBaseRingHom iC iC' iM iM' e eC hC hM) := by
  let _ := iC; let _ := iC'; let _ := iM; let _ := iM'
  refine Function.bijective_iff_has_inverse.2
    ⟨tensorBaseRingHom iC' iC iM' iM e.symm eC.symm
      (tensorBaseRing_hC_symm iC iC' e eC hC) (tensorBaseRing_hM_symm iM iM' e hM), ?_, ?_⟩
  · intro x
    induction x using TensorProduct.inductionOn with
    | tmul c m => rw [tensorBaseRingHom_tmul, tensorBaseRingHom_tmul, eC.symm_apply_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · intro x
    induction x using TensorProduct.inductionOn with
    | tmul c m => rw [tensorBaseRingHom_tmul, tensorBaseRingHom_tmul, eC.apply_symm_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

end TensorTransport

/-! ### The affine base change, with no site in sight -/

section BaseChange

variable (S : Scheme.{u}) (G : S.Modules) [G.IsQuasicoherent]

/-- **The affine sections of an associated module are a base change**, in a form that mentions
no site: the comparison `c ⊗ m ↦ c · m|` is bijective, for any identification of the base ring
with the global functions on the target. -/
theorem exists_bijective_sectionsBaseChange {W W₀ : Over S} (g : W ⟶ W₀)
    [IsAffine W.left] [IsAffine W₀.left]
    {R Cc : Type u} [CommRing R] [AddCommGroup Cc]
    (iC : Module R Cc)
    (iM : Module R (Γ((Scheme.Modules.pullback W₀.hom).obj G, ⊤) : Type u))
    (φ : Γ(W₀.left, ⊤) →+* Γ(W.left, ⊤))
    (hφ : φ = (g.left.appLE ⊤ ⊤ (Stacks.Sites.top_le_preimage_top g.left)).hom)
    (e : R ≃+* Γ(W₀.left, ⊤)) (eC : Cc ≃+ Γ(W.left, ⊤))
    (hC : ∀ (r : R) (c : Cc), eC (@HSMul.hSMul R Cc Cc _ r c) =
      @HSMul.hSMul Γ(W₀.left, ⊤)
        (((ModuleCat.restrictScalars φ).obj
          (ModuleCat.of Γ(W.left, ⊤) Γ(W.left, ⊤))) : Type u) _ _ (e r) (eC c))
    (hM : ∀ (r : R) (m : (Γ((Scheme.Modules.pullback W₀.hom).obj G, ⊤) : Type u)),
      @HSMul.hSMul R _ _ _ r m = @HSMul.hSMul Γ(W₀.left, ⊤) _ _ _ (e r) m) :
    ∃ Ψ : (@TensorProduct R _ Cc
          (Γ((Scheme.Modules.pullback W₀.hom).obj G, ⊤) : Type u) _ _ iC iM) →+
        (Γ((Scheme.Modules.pullback W.hom).obj G, ⊤) : Type u),
      Function.Bijective Ψ ∧
        ∀ (c : Cc) (m : (Γ((Scheme.Modules.pullback W₀.hom).obj G, ⊤) : Type u)),
          Ψ (@TensorProduct.tmul R _ Cc _ _ _ iC iM c m) =
            eC c • AlgebraicGeometry.pullbackSectionsMap G g m := by
  let N := (Scheme.Modules.pullback W₀.hom).obj G
  let T := tensorBaseRingHom iC
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of Γ(W.left, ⊤) Γ(W.left, ⊤))).isModule iM
    (ModuleCat.of Γ(W₀.left, ⊤) Γ((Scheme.Modules.pullback W₀.hom).obj G, ⊤)).isModule
    e eC hC hM
  let bc := Stacks.Sites.affineBaseChangeIsoOfEq N g.left φ hφ
  let cmp := AlgebraicGeometry.sectionsLinearEquivOfIso
    (Stacks.Sites.pullbackSectionsComparison G g) ⊤
  refine ⟨AddMonoidHom.comp cmp.toLinearMap.toAddMonoidHom
    (AddMonoidHom.comp bc.hom.hom.toAddMonoidHom T), ?_, ?_⟩
  · exact cmp.bijective.comp
      ((ConcreteCategory.bijective_of_isIso bc.hom).comp
        (bijective_tensorBaseRingHom _ _ _ _ _ _ _ _))
  · intro c m
    have h2 := Stacks.Sites.affineBaseChangeIsoOfEq_tmul N g.left φ hφ (eC c) m
    have h3 := Stacks.Sites.affineBaseChangeIsoOfEq_one_tmul N g.left φ hφ m
    have h4 := Stacks.Sites.pullbackSectionsComparison_pullbackSection G g
      (Stacks.Sites.top_le_preimage_top g.left) m
    have hstep := (congrArg (fun y => cmp y) h2).trans
      ((map_smul cmp (eC c) _).trans
        (congrArg (fun y => eC c • y) ((congrArg (fun y => cmp y) h3).trans h4)))
    exact hstep

end BaseChange

/-- Two additive maps out of a tensor product which agree on pure tensors agree everywhere. -/
private theorem tensor_apply_eq_of_tmul {R M N P F G : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N]
    [FunLike F (M ⊗[R] N) P] [AddMonoidHomClass F (M ⊗[R] N) P]
    [FunLike G (M ⊗[R] N) P] [AddMonoidHomClass G (M ⊗[R] N) P] {f : F} {g : G}
    (h : ∀ (c : M) (m : N), f (c ⊗ₜ[R] m) = g (c ⊗ₜ[R] m)) (x : M ⊗[R] N) : f x = g x := by
  induction x using TensorProduct.inductionOn with
  | tmul c m => exact h c m
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ### The comparison with a module extension -/

/-- The identification of a ring with the global functions on its spectrum, as a ring
isomorphism. -/
noncomputable def gammaSpecRingEquiv (R : CommRingCat.{u}) : ↥R ≃+* Γ(Spec R, ⊤) where
  toFun := (Scheme.ΓSpecIso R).inv
  invFun := (Scheme.ΓSpecIso R).hom
  left_inv x := congrArg (fun φ => (CommRingCat.Hom.hom φ) x) (Scheme.ΓSpecIso R).inv_hom_id
  right_inv x := congrArg (fun φ => (CommRingCat.Hom.hom φ) x) (Scheme.ΓSpecIso R).hom_inv_id
  map_mul' := map_mul _
  map_add' := map_add _

/-! ### The comparison with a module extension -/

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S) (A : CommRingCat.{u})
  (f : Spec A ⟶ S) (hA : schemeSizeBelow B.cutoff (Spec A))

/-- **The base ring as an algebra of the site.** This is the only use of the hypothesis that
`Spec A` is an object of the site. -/
def baseSiteAlgebra : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff) :=
  ⟨CommAlgCat.of A A, hA⟩

variable (F : SheafOfModules.{u} B.structureSheaf)

/-- The sections of `𝓕` over the base affine, as a module over the base ring. -/
noncomputable abbrev affineBaseSections : ModuleCat.{u} A :=
  ((affineSectionsFunctor.{u, u} B A f).obj F).obj (op (op (baseSiteAlgebra B A hA)))

/-- The structure morphism from the base algebra to an algebra of the site. -/
def baseSiteAlgebraHom (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    baseSiteAlgebra B A hA ⟶ X :=
  ObjectProperty.homMk (CommAlgCat.ofHom (Algebra.ofId A X.obj))

/-- Restriction of a section over the base affine to an affine of the site. -/
noncomputable def affineBaseRestrict
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (m : affineBaseSections B A f hA F) :
    ((affineSectionsFunctor.{u, u} B A f).obj F).obj (op (op X)) :=
  ((affineSectionsFunctor.{u, u} B A f).obj F).map ((baseSiteAlgebraHom B A hA X).op.op) m

/-- Restriction from the base affine sends `0` to `0`. -/
theorem affineBaseRestrict_zero
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    affineBaseRestrict B A f hA F X 0 = 0 := map_zero _

/-- Restriction from the base affine is additive. -/
theorem affineBaseRestrict_add
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (m n : affineBaseSections B A f hA F) :
    affineBaseRestrict B A f hA F X (m + n) =
      affineBaseRestrict B A f hA F X m + affineBaseRestrict B A f hA F X n := map_add _ _ _

/-- **Restriction from the base affine is the restriction map of `𝓕` itself**, stated once and
generically in `𝓕`. It holds by `rfl`: unfolding `Stacks.Adequate.affineSectionsFunctor` and
`PresheafOfModules.pushforward` is all it takes, and with `𝓕` a variable neither side can be
reduced any further. Consumers should rewrite with this rather than repeat the identification at
a specific sheaf, where the same `rfl` is over the heartbeat budget; see the module
documentation. -/
theorem affineBaseRestrict_val
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (m : affineBaseSections B A f hA F) :
    affineBaseRestrict B A f hA F X m =
      F.val.map ((affineSpecOver B A f).map (baseSiteAlgebraHom B A hA X).op).op m := rfl

/-- **The bridge which lets `Stacks.Adequate.affineBaseRestrict_val` compose with a statement
about a specific sheaf.** Restriction from the base affine agrees with any section `t` of `𝓕`
over the affine of `X` which the restriction map of `𝓕` produces.

The point is entirely one of elaboration cost, and the shape is what makes it work. The two
spellings of a restricted section do not carry the same type: `PresheafOfModules.map` lands in
`(ModuleCat.restrictScalars φ).obj (𝓕(Spec C))` over the structure sheaf, while the
affine-section functor's value carries *two* such layers over the algebra diagram of the site.
Both `Stacks.Adequate.affineBaseRestrict_val` and
`Stacks.Adequate.associatedModule_val_map_eq` are cheap on their own, but every direct
composition of them — `Eq.trans`, `rw`, `simp only`, a type ascription, a plain `rfl` — asks the
unifier to identify those two types at a *specific* sheaf and a *specific* morphism of the site,
and that is far over the heartbeat budget: the ring presheaves differ, congruence on
`ModuleCat.restrictScalars` fails, and the unifier descends into
`Stacks.Sites.associatedPresheaf`.

Here the identification is performed once, with the sheaf `𝓕` and the morphism `k` both
variables, where it is the millisecond `rfl` of `Stacks.Adequate.affineBaseRestrict_val`. The
target `t` is given in the plain spelling `𝓕(Spec C)`, so a consumer supplies `h` at an abstract
`k` — obtained by generalising the structure morphism, `obtain ⟨k, hk⟩ : ∃ k, _ = k := ⟨_, rfl⟩`
— and specialises `k` only afterwards, by which point no type remains to be identified. See
`Stacks.Adequate.affineBaseRestrict_associatedModule` for that use. Mathlib's
`ModuleCat.restrictScalarsCongr` does not apply: it compares restriction along two ring maps
between the *same* pair of rings, and the two ring presheaves here are different. -/
theorem affineBaseRestrict_eq_of_val_map
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (k : (affineSpecOver B A f).obj (op X) ⟶
      (affineSpecOver B A f).obj (op (baseSiteAlgebra B A hA)))
    (hk : (affineSpecOver B A f).map (baseSiteAlgebraHom B A hA X).op = k)
    (m : affineBaseSections B A f hA F)
    (t : ↥(F.val.obj (op ((affineSpecOver B A f).obj (op X)))))
    (h : F.val.map k.op m = t) :
    affineBaseRestrict B A f hA F X m = t := by
  subst hk
  exact (affineBaseRestrict_val B A f hA F X m).trans h

/-- Restriction to an affine of the site is semilinear over the structure map of its
algebra. -/
theorem affineBaseRestrict_smul
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) (r : ↥A)
    (m : affineBaseSections B A f hA F) :
    affineBaseRestrict B A f hA F X (r • m) =
      algebraMap ↥A ↥X.obj r • affineBaseRestrict B A f hA F X m :=
  PresheafOfModules.map_smul _ _ _ _

/-- The bilinear data of the comparison: `(c, m) ↦ c · m|`. -/
noncomputable def affineSectionsBilin
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    ↥X.obj →+ (affineBaseSections B A f hA F →+
      (((affineSectionsFunctor.{u, u} B A f).obj F).obj (op (op X)) : Type u)) where
  toFun c :=
    { toFun := fun m => c • affineBaseRestrict B A f hA F X m
      map_zero' := by rw [affineBaseRestrict_zero, smul_zero]
      map_add' := fun x y => by rw [affineBaseRestrict_add, smul_add] }
  map_zero' := AddMonoidHom.ext fun m => zero_smul _ _
  map_add' a b := AddMonoidHom.ext fun m => add_smul _ _ _

/-- The bilinear data is balanced over the base ring, so it descends to the tensor product. -/
theorem affineSectionsBilin_balanced
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (r : ↥A) (c : ↥X.obj) (m : affineBaseSections B A f hA F) :
    affineSectionsBilin B A f hA F X (r • c) m =
      affineSectionsBilin B A f hA F X c (r • m) := by
  change (r • c) • affineBaseRestrict B A f hA F X m =
    c • affineBaseRestrict B A f hA F X (r • m)
  rw [affineBaseRestrict_smul, smul_smul, Algebra.smul_def, mul_comm]

/-- The comparison at one algebra of the site, as an additive map. -/
noncomputable def affineSectionsCompareFun
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    TensorProduct ↥A ↥X.obj (affineBaseSections B A f hA F) →+
      (((affineSectionsFunctor.{u, u} B A f).obj F).obj (op (op X)) : Type u) :=
  TensorProduct.liftAddHom (affineSectionsBilin B A f hA F X)
    (affineSectionsBilin_balanced B A f hA F X)

/-- The comparison map sends `c ⊗ₜ m` to `c` times the restriction of `m`. -/
@[simp] theorem affineSectionsCompareFun_tmul
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (c : ↥X.obj) (m : affineBaseSections B A f hA F) :
    affineSectionsCompareFun B A f hA F X (c ⊗ₜ[↥A] m) =
      c • affineBaseRestrict B A f hA F X m := rfl

/-- The comparison map is linear over the algebra of the site. -/
theorem affineSectionsCompareFun_smul
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) (c : ↥X.obj)
    (x : TensorProduct ↥A ↥X.obj (affineBaseSections B A f hA F)) :
    affineSectionsCompareFun B A f hA F X (c • x) =
      c • affineSectionsCompareFun B A f hA F X x := by
  induction x using TensorProduct.inductionOn with
  | tmul d m =>
      rw [TensorProduct.smul_tmul', affineSectionsCompareFun_tmul,
        affineSectionsCompareFun_tmul, smul_eq_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The comparison at one algebra of the site. -/
noncomputable def affineSectionsCompareApp
    (X : ((AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ)ᵒᵖ) :
    ((AdequateFunctor.moduleExtensionFunctorOn
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).obj
          (affineBaseSections B A f hA F)).obj X ⟶
      ((affineSectionsFunctor.{u, u} B A f).obj F).obj X :=
  ModuleCat.homEquiv.symm
    { toFun := affineSectionsCompareFun B A f hA F X.unop.unop
      map_add' := map_add _
      map_smul' := fun c x => affineSectionsCompareFun_smul B A f hA F X.unop.unop c x }

/-- Any morphism of algebras of the site is a morphism under the base algebra. -/
theorem baseSiteAlgebraHom_comp
    {X Y : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)} (g : X ⟶ Y) :
    baseSiteAlgebraHom B A hA X ≫ g = baseSiteAlgebraHom B A hA Y := by
  ext

/-- Restricting a section over the base affine twice is restricting it once. -/
theorem affineBaseRestrict_naturality
    {X Y : ((AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ)ᵒᵖ} (g : X ⟶ Y)
    (m : affineBaseSections B A f hA F) :
    ((affineSectionsFunctor.{u, u} B A f).obj F).map g
        (affineBaseRestrict B A f hA F X.unop.unop m) =
      affineBaseRestrict B A f hA F Y.unop.unop m :=
  have h : (baseSiteAlgebraHom B A hA X.unop.unop).op.op ≫ g =
      (baseSiteAlgebraHom B A hA Y.unop.unop).op.op :=
    congrArg (fun p => p.op.op)
      (baseSiteAlgebraHom_comp B A hA (X := X.unop.unop) (Y := Y.unop.unop) g.unop.unop)
  (PresheafOfModules.map_comp_apply ((affineSectionsFunctor.{u, u} B A f).obj F)
      (baseSiteAlgebraHom B A hA X.unop.unop).op.op g m).symm.trans
    (PresheafOfModules.congr_map_apply ((affineSectionsFunctor.{u, u} B A f).obj F) h m)

/-- **The comparison `C ⊗_A 𝓕(Spec A) ⟶ F_{𝓕, A}`**, as a morphism of module-valued
functors. -/
noncomputable def affineSectionsCompare :
    (AdequateFunctor.moduleExtensionFunctorOn
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).obj
          (affineBaseSections B A f hA F) ⟶
      (affineSectionsFunctor.{u, u} B A f).obj F where
  app X := affineSectionsCompareApp B A f hA F X
  naturality {X Y} g := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul c m =>
        refine Eq.symm (Eq.trans (PresheafOfModules.map_smul
          ((affineSectionsFunctor.{u, u} B A f).obj F) g c
          (affineBaseRestrict B A f hA F X.unop.unop m)) ?_)
        rw [affineBaseRestrict_naturality]
        rfl
    | add x y hx hy =>
        exact ((map_add _ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add _ x y).symm

/-- **The module map underlying a map of sheaves of modules**: its component over the base
affine. -/
noncomputable def affineBaseSectionsMap {F F' : SheafOfModules.{u} B.structureSheaf}
    (u : F ⟶ F') : affineBaseSections B A f hA F ⟶ affineBaseSections B A f hA F' :=
  ((affineSectionsFunctor.{u, u} B A f).map u).app (op (op (baseSiteAlgebra B A hA)))

/-- A map of sheaves of modules commutes with restriction from the base affine. -/
theorem affineBaseRestrict_map {F F' : SheafOfModules.{u} B.structureSheaf} (u : F ⟶ F')
    (X : ((AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ)ᵒᵖ)
    (m : affineBaseSections B A f hA F) :
    ((affineSectionsFunctor.{u, u} B A f).map u).app X
        (affineBaseRestrict B A f hA F X.unop.unop m) =
      affineBaseRestrict B A f hA F' X.unop.unop (affineBaseSectionsMap B A f hA u m) :=
  PresheafOfModules.naturality_apply ((affineSectionsFunctor.{u, u} B A f).map u)
    (baseSiteAlgebraHom B A hA X.unop.unop).op.op m

/-- **The comparison is natural in the sheaf of modules.** This costs nothing beyond linearity
of a map of sheaves of modules and its commuting with restriction: the comparison is given by
the formula `c ⊗ m ↦ c · m|` for every sheaf. -/
theorem affineSectionsCompare_naturality {F F' : SheafOfModules.{u} B.structureSheaf}
    (u : F ⟶ F') :
    affineSectionsCompare B A f hA F ≫ (affineSectionsFunctor.{u, u} B A f).map u =
      (AdequateFunctor.moduleExtensionFunctorOn
          (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).map
            (affineBaseSectionsMap B A f hA u) ≫ affineSectionsCompare B A f hA F' := by
  ext X x
  refine tensor_apply_eq_of_tmul (fun c m => ?_) x
  refine Eq.trans ((((affineSectionsFunctor.{u, u} B A f).map u).app X).hom.map_smul c
    (affineBaseRestrict B A f hA F X.unop.unop m)) ?_
  rw [affineBaseRestrict_map]
  rfl

/-! ### The comparison is an isomorphism for an associated module -/

/-- The object of `Over S` underlying an algebra of the site. -/
noncomputable abbrev overOfAlg (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    Over S := B.toOver.obj ((affineSpecOver B A f).obj (op X))

/-- The scheme underlying an algebra of the site is affine: it is its spectrum. -/
instance isAffine_overOfAlg_left
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    IsAffine (overOfAlg B A f X).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of ↥X.obj)))

/-- The morphism of `Over S` from an algebra of the site down to the base algebra. -/
noncomputable abbrev overMapOfAlg
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    overOfAlg B A f X ⟶ overOfAlg B A f (baseSiteAlgebra B A hA) :=
  B.toOver.map ((affineSpecOver B A f).map (baseSiteAlgebraHom B A hA X).op)

/-- The ring map the affine base change is taken along. -/
noncomputable abbrev baseChangeRingMap
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :=
  ((overMapOfAlg B A f hA X).left.appLE ⊤ ⊤
    (Stacks.Sites.top_le_preimage_top (overMapOfAlg B A f hA X).left)).hom

/-- The global functions on the scheme of an algebra of the site are the algebra itself. -/
noncomputable def algGammaRingEquiv
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    ↥X.obj ≃+* Γ((overOfAlg B A f X).left, ⊤) :=
  gammaSpecRingEquiv (CommRingCat.of ↥X.obj)

/-- The global functions on the base affine are the base ring itself. -/
noncomputable def baseGammaRingEquiv :
    ↥A ≃+* Γ((overOfAlg B A f (baseSiteAlgebra B A hA)).left, ⊤) :=
  gammaSpecRingEquiv (CommRingCat.of ↥A)

/-- Under the identifications of global functions with the algebras, the ring map
`baseChangeRingMap` is the structure map `algebraMap A X`. -/
theorem baseChangeRingMap_gammaSpec
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) (a : ↥A) :
    baseChangeRingMap B A f hA X (baseGammaRingEquiv B A f hA a) =
      algGammaRingEquiv B A f X (algebraMap ↥A ↥X.obj a) :=
  have h := congrArg (fun φ => (CommRingCat.Hom.hom φ) a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ↥A ↥X.obj)))
  have hle := Stacks.Sites.gammaMap_eq_appLE_top_top (overMapOfAlg B A f hA X).left
  Eq.trans (congrArg (fun (φ : Γ((overOfAlg B A f (baseSiteAlgebra B A hA)).left, ⊤) →+*
      Γ((overOfAlg B A f X).left, ⊤)) =>
    φ (baseGammaRingEquiv B A f hA a)) hle.symm) h.symm

variable (G : S.Modules) [G.IsQuasicoherent]
  (hG : Presheaf.IsSheaf B.topology (Stacks.Sites.associatedPresheaf S G B.toOver))

/-- The sections of `Gᵃ` over the base affine, over its own ring of global functions. -/
noncomputable abbrev assocBaseSections :
    ModuleCat.{u} Γ((overOfAlg B A f (baseSiteAlgebra B A hA)).left, ⊤) :=
  ModuleCat.of Γ((overOfAlg B A f (baseSiteAlgebra B A hA)).left, ⊤)
    Γ((Scheme.Modules.pullback (overOfAlg B A f (baseSiteAlgebra B A hA)).hom).obj G, ⊤)

/-- The sections of `Gᵃ` over the base affine form a module over the global functions of the
base affine. -/
noncomputable instance moduleGammaAffineBaseSections :
    Module Γ((overOfAlg B A f (baseSiteAlgebra B A hA)).left, ⊤)
      (affineBaseSections B A f hA (B.associatedModule G hG) : Type u) :=
  (assocBaseSections B A f hA G).isModule

/-- The action of `a : A` on the sections of `Gᵃ` over the base affine is the action of the
corresponding global function `baseGammaRingEquiv a`. -/
theorem affineBaseSections_smul_eq
    (a : ↥A) (m : affineBaseSections B A f hA (B.associatedModule G hG)) :
    @HSMul.hSMul ↥A (affineBaseSections B A f hA (B.associatedModule G hG) : Type u) _ _ a m =
      @HSMul.hSMul Γ((overOfAlg B A f (baseSiteAlgebra B A hA)).left, ⊤)
        (assocBaseSections B A f hA G : Type u) _ _ (baseGammaRingEquiv B A f hA a) m := rfl

/-- Under `algGammaRingEquiv`, the action of `a : A` on `X` corresponds to the action of
`baseGammaRingEquiv a` on the global functions of `X` by restriction of scalars. -/
theorem assocBaseChangeFactor_smul_eq
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) (a : ↥A) (c : ↥X.obj) :
    algGammaRingEquiv B A f X (@HSMul.hSMul ↥A ↥X.obj _ _ a c) =
      @HSMul.hSMul Γ((overOfAlg B A f (baseSiteAlgebra B A hA)).left, ⊤)
        (((ModuleCat.restrictScalars (((overMapOfAlg B A f hA X).left.appLE ⊤ ⊤
              (Stacks.Sites.top_le_preimage_top
                (overMapOfAlg B A f hA X).left)).hom)).obj
            (ModuleCat.of Γ((overOfAlg B A f X).left, ⊤)
              Γ((overOfAlg B A f X).left, ⊤))) : Type u) _ _
        (baseGammaRingEquiv B A f hA a) (algGammaRingEquiv B A f X c) := by
  change _ = baseChangeRingMap B A f hA X (baseGammaRingEquiv B A f hA a) *
    algGammaRingEquiv B A f X c
  rw [baseChangeRingMap_gammaSpec, Algebra.smul_def, map_mul]

/-- The sections of `Gᵃ` over the affine of an algebra of the site, over its own ring of global
functions. This is `Stacks.Adequate.assocBaseSections` at a general algebra rather than at the
base. -/
noncomputable abbrev assocSections
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    ModuleCat.{u} Γ((overOfAlg B A f X).left, ⊤) :=
  ModuleCat.of Γ((overOfAlg B A f X).left, ⊤)
    Γ((Scheme.Modules.pullback (overOfAlg B A f X).hom).obj G, ⊤)

/-- The affine sections of `Gᵃ` over an algebra of the site, as a module over the global
functions on that affine. The affine-section functor presents them as a module over the algebra
itself; the two differ by the identification `Stacks.Adequate.algGammaRingEquiv`, so the instance
is supplied rather than inferred. -/
noncomputable instance moduleGammaAffineSections
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    Module Γ((overOfAlg B A f X).left, ⊤)
      ((((affineSectionsFunctor.{u, u} B A f).obj (B.associatedModule G hG)).obj
        (op (op X))) : Type u) :=
  (assocSections B A f G X).isModule

/-- **The two scalar actions on the affine sections of `Gᵃ` agree**, at a general algebra of the
site: acting through the algebra is acting through its global functions. This is
`Stacks.Adequate.affineBaseSections_smul_eq` one level up — there the base ring `A` acts through
`Γ(Spec A, 𝒪)`, here the algebra of `X` acts through `Γ(Spec X, 𝒪)` — and it is what lets the
comparison `c ⊗ m ↦ c · m|` be compared with the affine base change, whose scalars are the
global functions. Both actions are in scope, so each is written with its carrier explicit. -/
theorem affineSections_smul_eq
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) (c : ↥X.obj)
    (y : ((((affineSectionsFunctor.{u, u} B A f).obj (B.associatedModule G hG)).obj
      (op (op X))) : Type u)) :
    @HSMul.hSMul ↥X.obj
        ((((affineSectionsFunctor.{u, u} B A f).obj (B.associatedModule G hG)).obj
          (op (op X))) : Type u) _ _ c y =
      @HSMul.hSMul Γ((overOfAlg B A f X).left, ⊤) (assocSections B A f G X : Type u) _ _
        (algGammaRingEquiv B A f X c) y := rfl

/-! ### The comparison is an isomorphism for an associated module -/

/-- The restriction maps of an associated module are the pullback maps on sections of
[Stacks, Tag 03DS], for any morphism of the site. -/
theorem associatedModule_val_map_eq {Z Z' : B.category} (k : Z' ⟶ Z)
    (m : (B.associatedModule G hG).val.obj (op Z)) :
    (B.associatedModule G hG).val.map k.op m =
      AlgebraicGeometry.pullbackSectionsMap G (B.toOver.map k) m :=
  congrArg (fun φ => (ConcreteCategory.hom φ) m)
    (Stacks.Sites.associatedPresheaf_map_eq S G B.toOver k.op)

/-- **The restriction maps of `𝓖ᵃ` out of the base affine are the pullback maps on sections**,
with the section written in the spelling the affine-section functor gives it.

The morphism `k` is left abstract on purpose. Instantiating it at
`(affineSpecOver B A f).map (baseSiteAlgebraHom B A hA X).op` — which is what turns this into
the statement about `Stacks.Adequate.affineBaseRestrict` — puts the unifier back into the
`ModuleCat.restrictScalars` congruence described in the module documentation. Keeping `k`
abstract here costs nothing and is cheap; so is passing a section in the affine-section
spelling, which is the point of stating it rather than using
`Stacks.Adequate.associatedModule_val_map_eq` directly. -/
theorem associatedModule_val_map_affineBase
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (k : (affineSpecOver B A f).obj (op X) ⟶
      (affineSpecOver B A f).obj (op (baseSiteAlgebra B A hA)))
    (m : affineBaseSections B A f hA (B.associatedModule G hG)) :
    (B.associatedModule G hG).val.map k.op m =
      AlgebraicGeometry.pullbackSectionsMap G (B.toOver.map k) m :=
  associatedModule_val_map_eq B G hG k m

/-- **Restriction of a section of `𝓖ᵃ` from the base affine is the pullback map on sections**,
with the section in the affine-section spelling and the restriction written as the restriction of
the affine-section functor. This is the composition of
`Stacks.Adequate.affineBaseRestrict_val` with `Stacks.Adequate.associatedModule_val_map_eq`, and
it is the identification which the comparison with a module extension needs at an associated
module: the left side is what `Stacks.Adequate.affineSectionsCompareFun` is built from, and the
right side is what the affine base change of
`Stacks.Adequate.exists_bijective_sectionsBaseChange` produces.

Both halves are cheap and every direct composition of them is far over the heartbeat budget; see
`Stacks.Adequate.affineBaseRestrict_eq_of_val_map`, which is what makes this provable, and the
module documentation for the measurement. The proof generalises the structure morphism of the
algebra to a variable `k` *before* invoking either half, so that the one expensive unification
never arises, and substitutes it back only once the statement is closed. The morphism is written
as `B.toOver.map _` rather than through `Stacks.Adequate.overMapOfAlg`: unfolding that
abbreviation is itself part of the unification this avoids. -/
theorem affineBaseRestrict_associatedModule
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (m : affineBaseSections B A f hA (B.associatedModule G hG)) :
    affineBaseRestrict B A f hA (B.associatedModule G hG) X m =
      AlgebraicGeometry.pullbackSectionsMap G
        (B.toOver.map ((affineSpecOver B A f).map (baseSiteAlgebraHom B A hA X).op)) m := by
  obtain ⟨k, hk⟩ : ∃ k, (affineSpecOver B A f).map (baseSiteAlgebraHom B A hA X).op = k :=
    ⟨_, rfl⟩
  have hd := affineBaseRestrict_eq_of_val_map B A f hA (B.associatedModule G hG) X k hk m _
    (associatedModule_val_map_eq B G hG k m)
  subst hk
  exact hd

/-! ### The affine sections of an associated module are a module extension -/

/-- **The comparison on generators, in the base-change spelling.** Composing
`Stacks.Adequate.affineSectionsCompareFun_tmul` with
`Stacks.Adequate.affineBaseRestrict_associatedModule` and
`Stacks.Adequate.affineSections_smul_eq` rewrites `c ⊗ m ↦ c · m|` into exactly the generator
formula that `Stacks.Adequate.exists_bijective_sectionsBaseChange` produces, which is what
identifies the two maps. -/
theorem affineSectionsCompareFun_tmul_pullback
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) (c : ↥X.obj)
    (m : affineBaseSections B A f hA (B.associatedModule G hG)) :
    affineSectionsCompareFun B A f hA (B.associatedModule G hG) X (c ⊗ₜ[↥A] m) =
      @HSMul.hSMul Γ((overOfAlg B A f X).left, ⊤) (assocSections B A f G X : Type u) _ _
        (algGammaRingEquiv B A f X c)
        (AlgebraicGeometry.pullbackSectionsMap G
          (B.toOver.map ((affineSpecOver B A f).map (baseSiteAlgebraHom B A hA X).op)) m) := by
  rw [affineSectionsCompareFun_tmul, affineSections_smul_eq,
    affineBaseRestrict_associatedModule]

/-- **The affine base change of Descent, Proposition 03DX, restated once in the affine-section
spelling.** `Stacks.Adequate.exists_bijective_sectionsBaseChange` mentions no site, so its
tensor product is formed over the `Γ`-spelling of the base sections, while
`Stacks.Adequate.affineSectionsCompareFun` is formed over the affine-section spelling. The two
are definitionally equal, but typeclass synthesis is reducible-only and does not bridge them, so
`Zero` and `AddCommMonoid` are not found on the far side and the module structure must be
supplied positionally.

The conversion is therefore performed **once**, here, at the top level, rather than inside a
proof: done once it costs nothing, while an induction over the tensor product that crosses the
two spellings at every step is over the heartbeat budget (the same argument with the
general statement used directly dies at `isDefEq` in the `add` case). Its three hypotheses are
`Stacks.Adequate.baseChangeRingMap_gammaSpec` — through
`Stacks.Adequate.assocBaseChangeFactor_smul_eq` — and
`Stacks.Adequate.affineBaseSections_smul_eq`, which is what those lemmas were stated for. -/
theorem exists_bijective_affineSectionsCompare
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    ∃ Ψ : (TensorProduct ↥A ↥X.obj
          (affineBaseSections B A f hA (B.associatedModule G hG))) →+
        ((((affineSectionsFunctor.{u, u} B A f).obj (B.associatedModule G hG)).obj
          (op (op X))) : Type u),
      Function.Bijective Ψ ∧
        ∀ (c : ↥X.obj) (m : affineBaseSections B A f hA (B.associatedModule G hG)),
          Ψ (c ⊗ₜ[↥A] m) =
            @HSMul.hSMul Γ((overOfAlg B A f X).left, ⊤) (assocSections B A f G X : Type u) _ _
              (algGammaRingEquiv B A f X c)
              (AlgebraicGeometry.pullbackSectionsMap G
                (B.toOver.map ((affineSpecOver B A f).map (baseSiteAlgebraHom B A hA X).op))
                m) := by
  let iMbase : Module ↥A
      ((Γ((Scheme.Modules.pullback
        (B.toOver.obj ((affineSpecOver B A f).obj (op (baseSiteAlgebra B A hA)))).hom).obj G,
          ⊤)) : Type u) :=
    (affineBaseSections B A f hA (B.associatedModule G hG)).isModule
  obtain ⟨Ψ, hbij, hgen⟩ := exists_bijective_sectionsBaseChange S G
    (B.toOver.map ((affineSpecOver B A f).map (baseSiteAlgebraHom B A hA X).op))
    (inferInstance : Module ↥A ↥X.obj) iMbase
    (baseChangeRingMap B A f hA X) rfl
    (baseGammaRingEquiv B A f hA) (algGammaRingEquiv B A f X).toAddEquiv
    (assocBaseChangeFactor_smul_eq B A f hA X)
    (affineBaseSections_smul_eq B A f hA G hG)
  exact ⟨Ψ, hbij, hgen⟩

/-- **The comparison `C ⊗_A 𝓖ᵃ(Spec A) ⟶ 𝓖ᵃ(Spec C)` is bijective at every algebra of the
site.** Both it and the affine base change are additive maps out of the same tensor product
agreeing on the generators `c ⊗ m`, so they are equal, and the base change is bijective. -/
theorem bijective_affineSectionsCompareFun
    (X : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    Function.Bijective (affineSectionsCompareFun B A f hA (B.associatedModule G hG) X) := by
  obtain ⟨Ψ, hbij, hgen⟩ := exists_bijective_affineSectionsCompare B A f hA G hG X
  have hEq : ∀ x, affineSectionsCompareFun B A f hA (B.associatedModule G hG) X x = Ψ x :=
    tensor_apply_eq_of_tmul fun c m =>
      (affineSectionsCompareFun_tmul_pullback B A f hA G hG X c m).trans (hgen c m).symm
  exact ⟨fun a b hab => hbij.1 ((hEq a).symm.trans (hab.trans (hEq b))),
    fun y => (hbij.2 y).imp fun x hx => (hEq x).trans hx⟩

/-- A morphism of presheaves of modules whose components are isomorphisms is an isomorphism:
the inverse components are again natural. -/
private theorem isIso_of_isIso_app {C : Type w} [Category.{w'} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} R} (ψ : M ⟶ N) (h : ∀ X, IsIso (ψ.app X)) : IsIso ψ := by
  have he : ψ = (PresheafOfModules.isoMk (fun X => asIso (ψ.app X))
      (fun {_ _} g => ψ.naturality g)).hom := PresheafOfModules.hom_ext (fun _ => rfl)
  rw [he]
  infer_instance

/-- The comparison with a module extension is an isomorphism at each algebra of the site. -/
instance isIso_affineSectionsCompareApp
    (X : ((AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ)ᵒᵖ) :
    IsIso (affineSectionsCompareApp B A f hA (B.associatedModule G hG) X) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (bijective_affineSectionsCompareFun B A f hA G hG X.unop.unop)

/-- **The affine sections of an associated module are a module extension.** The comparison
`Stacks.Adequate.affineSectionsCompare` is an isomorphism of module-valued functors, because it
is one at every algebra of the site. -/
instance isIso_affineSectionsCompare :
    IsIso (affineSectionsCompare B A f hA (B.associatedModule G hG)) :=
  isIso_of_isIso_app _ fun X => isIso_affineSectionsCompareApp B A f hA G hG X

/-! ### Tag 06VK: the affine sections of a map of associated modules -/

/-- **`Stacks.Adequate.AffineAssociatedSections`, discharged.** For every affine scheme `Spec A`
*of the site* over `S` and every map `𝓖ᵃ ⟶ 𝓗ᵃ` of associated modules of quasi-coherent
`𝒪_S`-modules, the induced map of affine-section functors *is* a map of module extensions: take
the two `A`-modules to be the sections over the base affine and the map to be the component of
`φ.hom` there.

The isomorphism of arrows is `Stacks.Adequate.affineSectionsCompare_naturality` — the comparison
`c ⊗ m ↦ c · m|` is natural in the sheaf of modules — read as a commuting square and inverted,
which is legitimate because each of its two vertical maps is an isomorphism
(`Stacks.Adequate.isIso_affineSectionsCompare`). That in turn is the clause of Descent,
Proposition 03DX computing the affine sections of an associated module as a base change.

This used to be the hypothesis `hsec` of
`Stacks.Adequate.isAdequate_of_isAssociatedKernel`; that implication of [Stacks, Tag 06VK] is
stated below, and now carries no such hypothesis. -/
theorem affineAssociatedSections : AffineAssociatedSections B := by
  intro φ A f hA
  have := φ.source_isQuasicoherent
  have := φ.target_isQuasicoherent
  refine ⟨affineBaseSections B A f hA (B.associatedModule φ.source φ.source_isSheaf),
    affineBaseSections B A f hA (B.associatedModule φ.target φ.target_isSheaf),
    affineBaseSectionsMap B A f hA φ.hom, ⟨?_⟩⟩
  exact (Arrow.isoMk' _ _
    (asIso (affineSectionsCompare B A f hA (B.associatedModule φ.source φ.source_isSheaf)))
    (asIso (affineSectionsCompare B A f hA (B.associatedModule φ.target φ.target_isSheaf)))
    (affineSectionsCompare_naturality B A f hA φ.hom)).symm

/-- **[Stacks, Tag 06VK], the implication from a kernel presentation to adequacy.** A sheaf of
modules on the big `τ`-site over `S` which is the kernel of a map `𝓖ᵃ ⟶ 𝓗ᵃ` of the associated
modules of two quasi-coherent `𝒪_S`-modules is an adequate `𝒪`-module.

Over every affine scheme `Spec A` of the site the affine-section functor of the kernel is the
kernel of the affine-section functors, because affine sections commute with finite limits;
`Stacks.Adequate.affineAssociatedSections` identifies the latter two with module extensions, so
the affine-section functor of `𝓕` is the kernel of a map of module extensions, which is adequacy
of a module-valued functor. Adequacy of `𝓕` follows because the affine open cover of `S` is a
`τ`-covering by affine schemes of the site.

This is stated here rather than next to
`Stacks.Adequate.IsAssociatedKernel` because the identification it used to assume is a theorem
of this module and not a hypothesis of the implication. -/
public theorem isAdequate_of_isAssociatedKernel (F : SheafOfModules.{u} B.structureSheaf)
    (h : IsAssociatedKernel B F) : IsAdequate B F := by
  obtain ⟨p⟩ := h
  refine isAdequate_of_forall_affineSectionFunctor B F fun A f hA => ?_
  obtain ⟨M, N, ψ, ⟨e⟩⟩ := affineAssociatedSections B p.toAssociatedModuleMap A f hA
  refine ⟨M, N, ψ, ⟨?_⟩⟩
  refine (AdequateFunctor.presheafOfModulesUliftIso _ _) ≪≫ ?_
  refine ((affineSectionsFunctor.{u, u} B A f).mapIso p.iso) ≪≫ ?_
  refine (PreservesKernel.iso (affineSectionsFunctor.{u, u} B A f) p.hom) ≪≫ ?_
  exact KernelFork.mapIsoOfIsLimit (limit.isLimit (parallelPair _ 0))
    (limit.isLimit (parallelPair _ 0)) e

/-- **[Stacks, Tag 06VK], the implication (3) ⇒ (1).** If there is a `τ`-covering
`{gᵢ : Sᵢ → S}` and for each `i` a presentation of `𝓕|_(Sch/Sᵢ)_τ` as the kernel of a map
`𝓖ᵢᵃ ⟶ 𝓗ᵢᵃ` of associated modules of quasi-coherent `𝒪_{Sᵢ}`-modules, then `𝓕` is adequate.

Each restriction is adequate by `Stacks.Adequate.isAdequate_of_isAssociatedKernel`, and adequacy
descends along the covering by `Stacks.Adequate.isAdequate_of_coveringPullback`. Since (5)
implies (2) and (2) implies (3) by taking the affine open covering of `S` as the `τ`-covering,
this is also the implication from each of those conditions to adequacy. -/
public theorem isAdequate_of_coveringAssociatedKernel
    (F : SheafOfModules.{u} B.structureSheaf)
    (I : Type (u + 1)) (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (hg : ∀ i, coveringMorphismProperty τ (g i))
    (hsurj : (⋃ i, Set.range (g i)) = Set.univ)
    (hker : ∀ i, IsAssociatedKernelOnPullback B F (g i)) :
    IsAdequate B F := by
  refine isAdequate_of_coveringPullback B F I T g hg hsurj fun i => ?_
  obtain ⟨hT, J, hJ, hchosen, hsh, -, h⟩ := hker i
  exact ⟨hT, J, hJ, hchosen, hsh, isAdequate_of_isAssociatedKernel _ _ h⟩

end Stacks.Adequate

end
