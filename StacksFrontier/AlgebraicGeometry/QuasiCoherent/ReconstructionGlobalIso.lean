module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlobalForm
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionRigidity

/-!
# Rigidity of the reconstruction pair over a non-affine target

`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor` is rigidity for two morphisms of **affine**
schemes: if inverse image along `g` followed by tensoring with an invertible module is
isomorphic to the same for `g'`, then `g = g'`.  The gluing step of [Stacks, Tag 0GPJ] needs it
for two morphisms into a scheme `X` that is only quasi-compact and quasi-separated.  This file
removes the affineness of the target.

Two things have to happen.  The target has to be localised: both morphisms must be shown to
factor through one affine open `U ⊆ X`, and the isomorphism of functors on `QCoh(𝒪_X)` must be
pushed down to one on `QCoh(𝒪_U)`.  The second is possible because restriction
`QCoh(𝒪_X) ⥤ QCoh(𝒪_U)` is a **localization** of categories by [Stacks, Tag 0GPH]
(`AlgebraicGeometry.quasicoherentRestriction_isLocalization`), so composing with it is a fully
faithful operation on functors out of `QCoh(𝒪_U)` and a natural isomorphism can be cancelled on
the left (`CategoryTheory.Localization.liftNatIso`).  The first is
`AlgebraicGeometry.range_subset_of_iso_pullbackTensorFunctor`: it needs no new topological input
either, because
step 2 of [Stacks, Tag 0GPJ] supplies a finitely presented quasi-coherent module `G` with
`Supp G = X \ U`, and the support of an inverse image of a module of finite type is the inverse
image of the support ([Stacks, Tag 056J]).  So `g^*G = 0` exactly when `g` lands in `U`, and the
isomorphism of functors transports that vanishing from `g` to `g'`.

## Main results

* `AlgebraicGeometry.supportSet_eq_empty_of_isZero` — a zero module has empty support.
* `AlgebraicGeometry.pullbackTensorFunctorQuasicoherentRestrictIso` — for a morphism
  `β : W ⟶ U` into an open subscheme of `S`, inverse image along `β ≫ U.ι` followed by
  tensoring is restriction to `U` followed by inverse image along `β` and tensoring.  This is
  the target-localisation comparison.
* `AlgebraicGeometry.range_subset_of_iso_pullbackTensorFunctor` — **the topological half**: if
  the two functors are isomorphic and `g` lands in a quasi-compact open `U`, so does `g'`.
* `AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset` — **rigidity with the
  target not affine**: for `W` affine and `X` quasi-compact and quasi-separated, two morphisms
  `g g' : W ⟶ X` with an isomorphism of the two inverse-image-and-tensor functors are equal, as
  soon as `g` lands in some affine open of `X`; nothing is assumed about `g'`.

## What this does and does not give for [Stacks, Tag 0GPJ]

The conclusion of [Stacks, Tag 0GPJ] is a single isomorphism `Y ≅ X` and a single invertible
module.  `AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover`
produces the charts, and `AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible`
glues them given two overlap compatibilities.  The main theorem here is the rigidity input to
the first of those compatibilities, with the target no longer required affine.  What is still
missing is listed in the implementation notes.

## Implementation notes

**Why the invertible modules are presented as modules and not as sheaves.**  The hypothesis of
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor` names the two invertible sheaves as the
inverse images along `W ≅ Spec Γ(W, ⊤)` of the sheaves associated to `Γ(W, ⊤)`-modules, which
is the form in which the affine reconstruction produces them.  That form is preserved by the
localisation carried out here — the *target* changes from `X` to `U`, the source `W` does not —
so the statement can keep it.  It would *not* survive shrinking the source, which is why the
source is still assumed affine; see below.

**What remains undischarged for the gluing step.**  All three obstructions this note originally
recorded are now closed, and the scheme half of 0GPJ is proved; see
`QuasiCoherent/ReconstructionGlobalSchemeIso.lean`.  The record of how, since the route is not
obvious from the statements:

1. *The source is still affine.*  **Closed**, by removing the restriction rather than working
   around it: `AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_isInvertible`
   (`QuasiCoherent/ReconstructionOverlapCompatible.lean:169`) needs neither an affine source nor
   the `(W.isoSpec)^*(M^~)` presentation.  The ingredient named here as absent — an invertible
   sheaf on an affine scheme being the sheaf of an invertible module — is
   `AlgebraicGeometry.exists_module_invertible_iso_pullback_tilde`
   (`QuasiCoherent/AffineInvertiblePresentation.lean:162`).  Covering the overlap by affine
   *opens* proved unnecessary: `Scheme.affineCover` with `Scheme.Cover.hom_ext` suffices, so
   neither `Scheme.hom_ext_of_forall` nor `IsCompact (V i ⊓ V j)` is needed.
2. *The hypothesis has to be produced from the reconstruction's charts.*  **Closed**:
   `AlgebraicGeometry.pullbackTensorFunctorOverlapIso`
   (`QuasiCoherent/ReconstructionOverlapComparison.lean:242`), with both hypotheses supplied for
   the charts themselves at `:403`.
3. *The mirror compatibility.*
   `AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible`
   needs the compatibility of the `(f i).inv` over `U i ⊓ U j` as well, and the one-sided
   version is false (the counterexample is in
   `StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGluedIso.lean`).  Obtaining it
   needs the inverse of the reconstruction pair, i.e. that the inverse of
   `pullbackTensorFunctor f.hom L` for an isomorphism `f` is
   `pullbackTensorFunctor f.inv` of an invertible sheaf, which is also not available.

**No hypothesis here amounts to the conclusion.**  The only hypothesis beyond the isomorphism of
functors is that `g` lands in an affine open, which is a statement about `g` alone; the
corresponding statement for `g'` is *proved*, not assumed, by
`AlgebraicGeometry.range_subset_of_iso_pullbackTensorFunctor`.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 56.6.4 (Tag 0GPH)](https://stacks.math.columbia.edu/tag/0GPH)
* [Stacks Project, Lemma 28.5.5 (Tag 056J)](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  Without this
the invertibility hypothesis below does not deliver
`Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence`.  The same list is declared in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean` for the same reason. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-! ### A zero module has empty support -/

/-- **A zero sheaf of modules has empty support.**  The stalk of the underlying sheaf of abelian
groups at any point is the image of a zero object under two additive functors, hence has only
one element. -/
theorem supportSet_eq_empty_of_isZero {X : Scheme.{u}} {M : X.Modules} (hM : IsZero M) :
    supportSet M = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨a, ha⟩ := hx
  exact ha ((AddCommGrpCat.subsingleton_of_isZero
    (Functor.map_isZero (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      (Functor.map_isZero (Scheme.Modules.toPresheaf X) hM))).elim a 0)

/-! ### Localising the target of `pullbackTensorFunctor` to an open -/

/-- **Inverse image along a morphism into an open subscheme, followed by tensoring, is
restriction to that open followed by the same construction over it.**  For `β : W ⟶ U` with
`U ⊆ S` open, `(β ≫ U.ι)^*(-) ⊗ N` is `(-)|_U` followed by `β^*(-) ⊗ N`.

The three steps are: the inclusion of the quasi-coherent modules composed with
`AlgebraicGeometry.quasicoherentRestriction` *is* the inclusion composed with
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, by
`CategoryTheory.ObjectProperty.liftCompιIso`; restriction along an open immersion is inverse
image, by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`; and two successive
inverse images compose, by `AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
def pullbackTensorFunctorQuasicoherentRestrictIso {W S : Scheme.{u}} (U : S.Opens)
    (β : W ⟶ U.toScheme) (N : SheafOfModules.{u} W.ringCatSheaf) :
    quasicoherentRestriction U.ι ⋙ pullbackTensorFunctor β N ≅
      pullbackTensorFunctor (β ≫ U.ι) N :=
  Functor.isoWhiskerRight
      ((SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).liftCompιIso
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent S.ringCatSheaf) ⋙
          Scheme.Modules.restrictFunctor U.ι)
        (fun M ↦ Scheme.Modules.isQuasicoherent_restrictFunctor U.ι M.obj))
      (Scheme.Modules.pullback β ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ W.presheaf
            (forget₂ CommRingCat RingCat) W.ringCatSheaf.2⟩).obj N) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent S.ringCatSheaf))
        (Scheme.Modules.restrictFunctorIsoPullback U.ι))
      (Scheme.Modules.pullback β ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ W.presheaf
            (forget₂ CommRingCat RingCat) W.ringCatSheaf.2⟩).obj N) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent S.ringCatSheaf))
      (Functor.isoWhiskerRight (Scheme.Modules.pullbackComp β U.ι)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ W.presheaf
            (forget₂ CommRingCat RingCat) W.ringCatSheaf.2⟩).obj N))

/-! ### The topological half: the second morphism lands where the first does -/

/-- **If the two inverse-image-and-tensor functors are isomorphic and the first morphism lands
in a quasi-compact open, so does the second.**  Let `S` be quasi-compact and quasi-separated,
let `g g' : W ⟶ S`, let `N` and `N'` be invertible sheaves of `𝒪_W`-modules and suppose
`g^*(-) ⊗ N ≅ g'^*(-) ⊗ N'` as functors on quasi-coherent `𝒪_S`-modules.  If the image of `g`
is contained in a quasi-compact open `U ⊆ S`, so is the image of `g'`.

Step 2 of [Stacks, Tag 0GPJ]
(`AlgebraicGeometry.exists_isFinitePresentation_supportSet_eq_compl`) gives a finitely presented
quasi-coherent module `G` with `Supp G = S \ U`.  Then `Supp (g^*G) = g^{-1}(S \ U) = ∅` by
[Stacks, Tag 056J], so `g^*G` is zero and so is `g^*G ⊗ N`; the isomorphism carries that to
`g'^*G ⊗ N'`, and tensoring with the invertible `N'` is an equivalence, so `g'^*G` is zero and
`g'^{-1}(S \ U)` is empty. -/
theorem range_subset_of_iso_pullbackTensorFunctor {W S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] (g g' : W ⟶ S) (N N' : SheafOfModules.{u} W.ringCatSheaf)
    [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N]
    [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N']
    (θ : pullbackTensorFunctor g N ≅ pullbackTensorFunctor g' N') (U : S.Opens)
    (hU : IsCompact (U : Set S)) (hg : Set.range g ⊆ (U : Set S)) :
    Set.range g' ⊆ (U : Set S) := by
  obtain ⟨G, hGfp, hGsupp⟩ := exists_isFinitePresentation_supportSet_eq_compl U hU
  have := hGfp
  -- `g^*G` has empty support, hence is zero.
  have hz : IsZero ((Scheme.Modules.pullback g).obj G.obj) := by
    refine Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _ ?_
    rw [Stacks.Modules.supp_pullback g G.obj,
      show SheafOfModules.supp G.obj = (U : Set S)ᶜ from hGsupp]
    exact Set.eq_empty_iff_forall_notMem.2 fun x hx => hx (hg ⟨x, rfl⟩)
  -- Tensoring with `N` is additive, so `g^*G ⊗ N` is zero too.
  have hz2 : IsZero ((pullbackTensorFunctor g N).obj G) :=
    Functor.map_isZero ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ W.presheaf
        (forget₂ CommRingCat RingCat) W.ringCatSheaf.2⟩).obj N) hz
  -- Transport along `θ` and reflect through the equivalence given by the invertible `N'`.
  have hz4 : IsZero ((Scheme.Modules.pullback g').obj G.obj) :=
    IsZero.of_full_of_faithful_of_isZero
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ W.presheaf
          (forget₂ CommRingCat RingCat) W.ringCatSheaf.2⟩).obj N') _
      ((θ.app G).isZero_iff.mp hz2)
  have hempty : (g' ⁻¹' (U : Set S)ᶜ) = ∅ := by
    rw [← show SheafOfModules.supp G.obj = (U : Set S)ᶜ from hGsupp,
      ← Stacks.Modules.supp_pullback g' G.obj]
    exact supportSet_eq_empty_of_isZero hz4
  rintro y ⟨x, rfl⟩
  by_contra hy
  exact (Set.eq_empty_iff_forall_notMem.1 hempty x) hy

/-! ### Rigidity with the target not affine -/

/-- **Rigidity of the reconstruction pair with the target only quasi-compact and
quasi-separated.**  Let `W` be an affine scheme, let `X` be quasi-compact and quasi-separated,
let `g g' : W ⟶ X` and let `L` and `M` be invertible `Γ(W, ⊤)`-modules.  If inverse image of
quasi-coherent modules along `g` followed by tensoring with the sheaf attached to `L` is
isomorphic to the same for `g'` and `M`, and the image of `g` lies in some affine open `U ⊆ X`,
then `g = g'`.

This is `AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor` with the affineness of the target
removed.  That `g'` also lands in `U` is
`AlgebraicGeometry.range_subset_of_iso_pullbackTensorFunctor`, so both morphisms factor through
`U`; restriction
`QCoh(𝒪_X) ⥤ QCoh(𝒪_U)` is a localization by [Stacks, Tag 0GPH], so the isomorphism of functors
descends to `QCoh(𝒪_U)` by `CategoryTheory.Localization.liftNatIso`, and `U` is affine. -/
theorem eq_of_iso_pullbackTensorFunctor_of_range_subset {W X : Scheme.{u}} [IsAffine W]
    [CompactSpace X] [QuasiSeparatedSpace X] (g g' : W ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (L M : ModuleCat.{u} Γ(W, ⊤)) [Module.Invertible Γ(W, ⊤) L] [Module.Invertible Γ(W, ⊤) M]
    (θ : pullbackTensorFunctor g ((Stacks.RingedSpace.pullbackFunctor
          W.isoSpec.hom.toLRSHom.toShHom).obj (tilde L)) ≅
        pullbackTensorFunctor g' ((Stacks.RingedSpace.pullbackFunctor
          W.isoSpec.hom.toLRSHom.toShHom).obj (tilde M)))
    (hg : Set.range g ⊆ (U : Set X)) :
    g = g' := by
  have hinv : ∀ (L : ModuleCat.{u} Γ(W, ⊤)) [Module.Invertible Γ(W, ⊤) L],
      Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
        ((Stacks.RingedSpace.pullbackFunctor W.isoSpec.hom.toLRSHom.toShHom).obj (tilde L)) :=
    fun L _ => @Stacks.RingedSpace.modulePullback_isInvertible _ _
      W.isoSpec.hom.toLRSHom.toShHom (tilde L) (isInvertible_tilde _ _)
  have := hinv L
  have := hinv M
  have hg' : Set.range g' ⊆ (U : Set X) :=
    range_subset_of_iso_pullbackTensorFunctor g g' _ _ θ U hU.isCompact hg
  have hlift : ∀ h : W ⟶ X, Set.range h ⊆ (U : Set X) → ∃ β : W ⟶ U.toScheme, β ≫ U.ι = h :=
    fun h hh => ⟨IsOpenImmersion.lift U.ι h (by rwa [Scheme.Opens.range_ι]),
      IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨β, hβ⟩ := hlift g hg
  obtain ⟨β', hβ'⟩ := hlift g' hg'
  subst hβ hβ'
  have : IsAffine U.toScheme := hU
  have hloc := quasicoherentRestriction_isLocalization X ((U : Set X)ᶜ) U
    (compl_compl _).symm hU.isCompact
  have θ' : quasicoherentRestriction U.ι ⋙ pullbackTensorFunctor β
        ((Stacks.RingedSpace.pullbackFunctor W.isoSpec.hom.toLRSHom.toShHom).obj (tilde L)) ≅
      quasicoherentRestriction U.ι ⋙ pullbackTensorFunctor β'
        ((Stacks.RingedSpace.pullbackFunctor W.isoSpec.hom.toLRSHom.toShHom).obj (tilde M)) :=
    pullbackTensorFunctorQuasicoherentRestrictIso U β _ ≪≫ θ ≪≫
      (pullbackTensorFunctorQuasicoherentRestrictIso U β' _).symm
  have hββ' : β = β' :=
    eq_of_iso_pullbackTensorFunctor β β' L M
      (Localization.liftNatIso (quasicoherentRestriction U.ι)
        (quasicoherentSupportedOn X ((U : Set X)ᶜ)).isoModSerre _ _
        (pullbackTensorFunctor β
          ((Stacks.RingedSpace.pullbackFunctor W.isoSpec.hom.toLRSHom.toShHom).obj (tilde L)))
        (pullbackTensorFunctor β'
          ((Stacks.RingedSpace.pullbackFunctor W.isoSpec.hom.toLRSHom.toShHom).obj (tilde M)))
        θ')
  rw [hββ']

end AlgebraicGeometry

end
