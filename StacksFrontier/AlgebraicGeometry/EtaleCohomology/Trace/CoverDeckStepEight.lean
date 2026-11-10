module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroDirectImageTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactificationStepNine

/-!
# Step 8 of the trace formula: the deck action on `j_! f_*` is a twisted Frobenius

Let `i : Z ⟶ Y` be an integral morphism of schemes over a finite field `k`, `jU : U ⟶ Y` an open
immersion with inverse image `jV : V ⟶ Z`, `f : V ⟶ U` the restriction of `i`, and `σ` an
endomorphism of `Z` over `Y` restricting to `a` on `V`.  For a bounded below complex `N` of
`Λ`-modules, `a` acts on `f_* j_V^{-1} N_Z` through the canonical twist `N_Z ⟶ σ_* N_Z` (the deck
transformation, when `f` is a Galois cover).  The canonical isomorphism
`j_!(f_* j_V^{-1} N_Z) ≅ i_*(j_{V!} j_V^{-1} N_Z)` carries `j_!` of this action to `i_*` of the
extension by zero of the canonical twist, so by
`perfectDerivedTrace_frobeniusTwist_directImage_eq_twistedFrobenius_of_commRing` the trace of the
Frobenius of `RΓ(Y_k̄, j_!(f_* j_V^{-1} N_Z))` composed with the action of `a` is the trace of the
twisted Frobenius `(σ̄ π̄)^*` on `RΓ(Z_k̄, (j_{V!} j_V^{-1} N_Z)|_{Z_k̄})`.  This is the second
equality of Step 8 of the proof of [Stacks, Tag 03UG] ("the Leray spectral sequence, using the
finiteness of `f`").  For a Galois cover of an open of a proper curve with
`U(k) = ∅` and `Z` the smooth compactification of the cover, Step 9
(`Stacks.EtaleCohomology.perfectDerivedTrace_twistedFrobenius_coverCompactification_eq_zero`) shows
that this trace vanishes.

## Main results

* `Stacks.EtaleCohomology.isIso_extensionByZeroDirectImageMap_of_isOpenImmersion`:
  `j_!(f_* M) ≅ i_*(j_{V!} M)` for open immersions.
* `Stacks.EtaleCohomology.openDeck`: the action of `a` on `f_* j_V^{-1} N_Z`.
* `Stacks.EtaleCohomology.openExtensionIso`, `Stacks.EtaleCohomology.openExtensionIso_deck`.
* `Stacks.EtaleCohomology.perfectDerivedTrace_openDeck_eq_twistedFrobenius` (Step 8).
* `Stacks.EtaleCohomology.perfectDerivedTrace_openDeck_coverCompactification_eq_zero`
  (Steps 8 and 9 for a Galois cover).

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 8 and 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

section OpenImmersion

variable (Λ : Type) [CommRing Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [IsOpenImmersion j]
  (j' : V ⟶ Vb) [IsOpenImmersion j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]
  (sq : IsPullback f j' j fb)

include sq in
/-- **The canonical map `j_!(f_* M) ⟶ f̄_*(j'_! M)` is an isomorphism** for open immersions `j`,
`j'` and `f̄` integral (with `V = V̄ ×_Ū U`). -/
theorem isIso_extensionByZeroDirectImageMap_of_isOpenImmersion (M : EtaleModules.{u, 0} Λ V) :
    IsIso (extensionByZeroDirectImageMap Λ j j' f fb sq M) := by
  set i := (Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : Closeds Ub)).subschemeι
  have hi : Set.range i.base = (Set.range j.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hij : Set.range j.base = (Set.range i.base)ᶜ := by rw [hi, compl_compl]
  have hj' : Set.range j'.base = fb.base ⁻¹' Set.range j.base := by
    have h := image_preimage_eq_of_isPullback sq Set.univ
    rwa [Set.preimage_univ, Set.image_univ, Set.image_univ] at h
  have hij' : Set.range j'.base = (Set.range (pullback.snd i fb).base)ᶜ := by
    rw [show Set.range (pullback.snd i fb).base = Set.range (pullback.snd i fb) from rfl,
      Scheme.Pullback.range_snd, show Set.range i = Set.range i.base from rfl, hi, hj',
      Set.preimage_compl, compl_compl]
  exact isIso_extensionByZeroDirectImageMap Λ j j' f fb sq i hij (pullback.snd i fb) hij'
    (pullback.fst i fb) (IsPullback.of_hasPullback i fb) M

end OpenImmersion

section Generic

variable {A B B' D E : Type*} [Category* A] [Category* B] [Category* B'] [Category* D]
  [Category* E] [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms B']
  [HasZeroMorphisms D] [HasZeroMorphisms E]

/-- The components of the image under `G` of a morphism of bounded below complexes. -/
lemma mapCochainComplexPlus_map_hom_f (G : D ⥤ E) [G.PreservesZeroMorphisms]
    {K L : CochainComplex.Plus D} (φ : K ⟶ L) (n : ℤ) :
    (G.mapCochainComplexPlus.map φ).hom.f n = G.map (φ.hom.f n) := rfl

/-- The components of an isomorphism of bounded below complexes built from components. -/
lemma isoMk_isoOfComponents_hom_hom_f {K L : CochainComplex.Plus D}
    (e : ∀ n, K.obj.X n ≅ L.obj.X n)
    (comm : ∀ i j, (ComplexShape.up ℤ).Rel i j → (e i).hom ≫ L.obj.d i j = K.obj.d i j ≫ (e j).hom)
    (n : ℤ) :
    (ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents e comm)).hom.hom.f n =
      (e n).hom := rfl

end Generic

section StepEight

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {Y Z : Over (Spec (.of k))}
  (i : Z ⟶ Y) [IsIntegralHom i.left] (σ : Z ⟶ Z) [IsIntegralHom σ.left] (hσ : σ ≫ i = i)
  {U V : Scheme.{u}} (jU : U ⟶ Y.left) [IsOpenImmersion jU] [Etale jU] [Mono jU]
  (jV : V ⟶ Z.left) [IsOpenImmersion jV] [Etale jV] [Mono jV]
  (f : V ⟶ U) (sq : IsPullback f jV jU i.left) (a : V ⟶ V) (ha : a ≫ f = f)
  (sqσ : IsPullback a jV jV σ.left)

omit [Fintype k] [IsIntegralHom σ.left] in
/-- The canonical twist `M_Z ⟶ σ_* M_Z` is natural in `M`. -/
lemma constantSelfMapTwist_naturality_left {M M' : ModuleCat.{u + 1} Λ} (x : M ⟶ M') :
    (constantSheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map x ≫
        constantSelfMapTwist Λ M' σ.left =
      constantSelfMapTwist Λ M σ.left ≫ (etaleModuleDirectImage.{u, 0} Λ σ.left).map
        ((constantSheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map x) := by
  simp only [constantSelfMapTwist]
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  exact (etaleModuleInverseImageConstantIso.{u, 0} Λ σ.left).hom.naturality x

/-- **The deck transformation `a` acting on `f_* j^{-1} M_Z`**: the restriction of the canonical
twist of `M_Z` along `σ`, pushed forward along `f`. -/
def openDeckHom (M : ModuleCat.{u + 1} Λ) :
    (etaleModuleDirectImage.{u, 0} Λ f).obj
        ((etaleModuleRestriction.{u, 0} Λ jV).obj (etaleModuleConstantSheaf Λ M Z.left)) ⟶
      (etaleModuleDirectImage.{u, 0} Λ f).obj
        ((etaleModuleRestriction.{u, 0} Λ jV).obj (etaleModuleConstantSheaf Λ M Z.left)) :=
  directImageTwist Λ f a ha
    ((etaleModuleRestriction.{u, 0} Λ jV).obj (etaleModuleConstantSheaf Λ M Z.left))
    (restrictionTwist Λ jV a σ.left sqσ (etaleModuleConstantSheaf Λ M Z.left)
      (constantSelfMapTwist Λ M σ.left))

omit [Fintype k] [IsOpenImmersion jV] [Mono jV] in
/-- The deck transformation `a` acting on `f_* j^{-1} M_Z` is natural in `M`. -/
lemma openDeckHom_naturality {M M' : ModuleCat.{u + 1} Λ} (x : M ⟶ M') :
    (etaleModuleDirectImage.{u, 0} Λ f).map ((etaleModuleRestriction.{u, 0} Λ jV).map
        ((constantSheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map x)) ≫
      openDeckHom Λ σ jV f a ha sqσ M' =
    openDeckHom Λ σ jV f a ha sqσ M ≫ (etaleModuleDirectImage.{u, 0} Λ f).map
      ((etaleModuleRestriction.{u, 0} Λ jV).map
        ((constantSheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map x)) :=
  directImageTwist_naturality Λ f a ha _ _ _
    (restrictionTwist_naturality Λ jV a σ.left sqσ _ _ _
      (constantSelfMapTwist_naturality_left Λ σ x))

/-- **The deck transformation `a` acting on `f_* j^{-1} (-)_Z`**, as a natural endomorphism. -/
def openDeckNatTrans :
    constantSheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        etaleModuleRestriction.{u, 0} Λ jV ⋙ etaleModuleDirectImage.{u, 0} Λ f ⟶
      constantSheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        etaleModuleRestriction.{u, 0} Λ jV ⋙ etaleModuleDirectImage.{u, 0} Λ f where
  app M := openDeckHom Λ σ jV f a ha sqσ M
  naturality _ _ x := openDeckHom_naturality Λ σ jV f a ha sqσ x

variable (N : CochainComplex.Plus (ModuleCat.{u + 1} Λ))

/-- The complex `f_* j^{-1} N_Z` on `U`. -/
abbrev openComplex : CochainComplex.Plus (EtaleModules.{u, 0} Λ U) :=
  (etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus.obj
    ((etaleModuleRestriction.{u, 0} Λ jV).mapCochainComplexPlus.obj
      ((constantSheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapCochainComplexPlus.obj N))

/-- **The deck transformation `a` acting on the complex `f_* j^{-1} N_Z`.** -/
def openDeck : openComplex Λ jV f N ⟶ openComplex Λ jV f N :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex (openDeckNatTrans Λ σ jV f a ha sqσ) _).app
    N.obj)

omit [Fintype k] [IsOpenImmersion jV] [Mono jV] in
/-- The components of the deck transformation. -/
lemma openDeck_hom_f (n : ℤ) :
    (openDeck Λ σ jV f a ha sqσ N).hom.f n = openDeckHom Λ σ jV f a ha sqσ (N.obj.X n) := rfl

/-- **The identification `j_!(f_* j^{-1} M_Z) ≅ i_*(j'_! j'^{-1} M_Z)`** on `Y`. -/
def openExtensionIsoApp (M : ModuleCat.{u + 1} Λ) :
    (etaleModuleExtensionByZero.{u, 0} Λ jU).obj ((etaleModuleDirectImage.{u, 0} Λ f).obj
        ((etaleModuleRestriction.{u, 0} Λ jV).obj (etaleModuleConstantSheaf Λ M Z.left))) ≅
      (etaleModuleDirectImage.{u, 0} Λ i.left).obj ((etaleModuleExtensionByZero.{u, 0} Λ jV).obj
        ((etaleModuleRestriction.{u, 0} Λ jV).obj (etaleModuleConstantSheaf Λ M Z.left))) :=
  haveI := isIso_extensionByZeroDirectImageMap_of_isOpenImmersion Λ jU jV f i.left sq
    ((etaleModuleRestriction.{u, 0} Λ jV).obj (etaleModuleConstantSheaf Λ M Z.left))
  asIso (extensionByZeroDirectImageMap Λ jU jV f i.left sq
    ((etaleModuleRestriction.{u, 0} Λ jV).obj (etaleModuleConstantSheaf Λ M Z.left)))

/-- **The identification `j_!(f_* j^{-1} N_Z) ≅ i_*(j'_! j'^{-1} N_Z)`** of complexes on `Y`. -/
def openExtensionIso :
    (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj (openComplex Λ jV f N) ≅
      (etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj
        (extensionByZeroConstantComplex Λ Z jV N) :=
  ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents
    (fun n => openExtensionIsoApp Λ i jU jV f sq (N.obj.X n))
    (fun _ _ _ => (extensionByZeroDirectImageMap_naturality Λ jU jV f i.left sq _).symm))

omit [Fintype k] [Mono jU] in
/-- The components of `Stacks.EtaleCohomology.openExtensionIso`. -/
lemma openExtensionIso_hom_hom_f (n : ℤ) :
    (openExtensionIso Λ i jU jV f sq N).hom.hom.f n =
      extensionByZeroDirectImageMap Λ jU jV f i.left sq
        ((etaleModuleRestriction.{u, 0} Λ jV).obj
          (etaleModuleConstantSheaf Λ (N.obj.X n) Z.left)) :=
  isoMk_isoOfComponents_hom_hom_f _ _ n

include hσ in
omit [Fintype k] in
/-- **The deck transformation is carried to the extension by zero of the twist**: under
`Stacks.EtaleCohomology.openExtensionIso`, `j_!` of the deck transformation is `i_*` of the
extension by zero of the canonical twist of `N_Z` along `σ`, followed by `i_* σ_* = i_*`. -/
lemma openExtensionIso_deck (n : ℤ) :
    ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.map
        (openDeck Λ σ jV f a ha sqσ N)).hom.f n ≫ (openExtensionIso Λ i jU jV f sq N).hom.hom.f n =
      (openExtensionIso Λ i jU jV f sq N).hom.hom.f n ≫
        (etaleModuleDirectImage.{u, 0} Λ i.left).map
          (extensionByZeroConstantTwist Λ Z σ jV a sqσ N n) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ σ.left i.left i.left
          (by rw [← Over.comp_left, hσ])).hom.app
            ((extensionByZeroConstantComplex Λ Z jV N).obj.X n) := by
  rw [mapCochainComplexPlus_map_hom_f, openDeck_hom_f, openExtensionIso_hom_hom_f, openDeckHom]
  exact extensionByZeroDirectImageMap_comp_extensionByZeroTwist Λ jU jV f i.left sq a σ.left sqσ
    (by rw [← Over.comp_left, hσ]) ha _ _

variable (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

include hσ sq in
/-- **Step 8 of [Stacks, Tag 03UG]**: for the open `V = i^{-1}(U)` of `Z` over the open `U` of
`Y` (with `i : Z ⟶ Y` integral), and an endomorphism `σ` of `Z` over `Y` restricting to `a` on
`V`, the trace of the Frobenius of `RΓ(Y_k̄, j_!(f_* j^{-1} N_Z))` composed with the deck
transformation `a` is the trace of the twisted Frobenius `(σ̄ π̄)^*` on
`RΓ(Z_k̄, (j_! j^{-1} N_Z)|_{Z_k̄})`. -/
theorem perfectDerivedTrace_openDeck_eq_twistedFrobenius
    (hY : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ
            (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
                (openComplex Λ jV f N))))))))
    (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ
            (pullback.snd Z.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ Z jV N))))))) :
    perfectDerivedTrace Λ ⟨_, hY⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
            (openComplex Λ jV f N)))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
              (openComplex Λ jV f N)))
          (Y := (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
                (openComplex Λ jV f N))))
          ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard) (ComplexShape.up ℤ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
              (openComplex Λ jV f N)).obj) ≫
          (etaleModuleDirectImage.{u, 0} Λ
              (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
              ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.map
                (openDeck Λ σ jV f a ha sqσ N)))))) =
      perfectDerivedTrace Λ ⟨_, hZ⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Z σ kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} Λ (twistedGeometricFrobenius Z σ kbar p q hcard)
          (pullback.snd Z.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius_comp_toBase Z σ kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
          (extensionByZeroConstantComplex Λ Z jV N))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
            (extensionByZeroConstantComplex Λ Z jV N))
          (Y := (etaleModuleDirectImage.{u, 0} Λ
            (twistedGeometricFrobenius Z σ kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ Z jV N)))
          (Functor.twistedBaseChangeTwistHC
            (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Z σ kbar p q hcard))
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar))
            (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Z kbar p q hcard))
            (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap σ kbar))
            (etaleModuleDirectImage.{u, 0} Λ σ.left)
            (frobeniusBaseChangeTwist.{u, 0} Λ Z kbar p q hcard)
            (automorphismBaseChange Λ Z σ kbar)
            (etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap σ kbar)
              (geometricFrobeniusBaseChange Z kbar p q hcard)
              (twistedGeometricFrobenius Z σ kbar p q hcard) rfl)
            (extensionByZeroConstantComplex Λ Z jV N).obj
            (extensionByZeroConstantTwist Λ Z σ jV a sqσ N)
            (extensionByZeroConstantTwist_comm Λ Z σ jV a sqσ N))))) :=
  perfectDerivedTrace_frobeniusTwist_directImage_eq_twistedFrobenius_of_commRing i σ hσ kbar p
    q hcard Λ _ _ _ _ _ (openExtensionIso Λ i jU jV f sq N)
    (openExtensionIso_deck Λ i σ hσ jU jV f sq a ha sqσ N) hY hZ

end StepEight

section CoverStepEight

variable {k : Type u} [Field k] [Fintype k] [PerfectField k] {U V : Scheme.{u}}
  {pU : U ⟶ Spec (.of k)} [IsCurve k pU] [Smooth pU] (Y : Over (Spec (.of k))) [IsProper Y.hom]
  {jU : U ⟶ Y.left} [IsOpenImmersion jU] (hjU : jU ≫ Y.hom = pU) {f : V ⟶ U} [IsFinite f]
  [Etale f] [ConnectedSpace V] (C : CoverCompactification k Y.hom jU f) (a : V ≅ V)
  (ha : a.hom ≫ f = f) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q) (Λ : Type) [CommRing Λ]
  (N : CochainComplex.Plus (ModuleCat.{u + 1} Λ))

omit [IsCurve k pU] [Smooth pU] [IsFinite f] [Etale f] in
include hjU in
/-- **Steps 8 and 9 of [Stacks, Tag 03UG] for a Galois cover.**  Let `f : V ⟶ U` be a connected
finite étale cover of an open `U` of a proper curve `Y` over the finite field `k`, smooth with
`U(k) = ∅`, with smooth projective compactification `V̄ ⟶ Y`, and `a` an automorphism of `V` over
`U`.  Granted perfectness and Weil's formula for the twisted Frobenius `σ̄_a π̄` of `V̄`, the
Frobenius of `RΓ(Y_k̄, j_!(f_* j'^{-1} N_{V̄}))` composed with the deck transformation `a` has
trace zero. -/
theorem perfectDerivedTrace_openDeck_coverCompactification_eq_zero
    [IsEmpty (rationalPoints pU)]
    (hY : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ
            (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
                (openComplex Λ (Z := C.toOver) C.j f N))))))))
    (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj C.toOver kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ C.toOver C.j N)))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ
        (pullback.snd C.toOver.hom (specAlgebraMap k kbar)) (etaleModuleConstantComplex Λ kbar N))))
    (hp₃ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ
        (pullback.snd C.boundaryOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex Λ kbar N))))
    (hΓ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex Λ (etaleModuleConstantComplex Λ kbar N).obj)))
    (hweil : perfectDerivedTrace Λ ⟨_, hp₂⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} Λ
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius C.toOver (C.extendOver hjU a ha) kbar p q hcard)
          (twistedGeometricFrobenius_comp_toBase C.toOver (C.extendOver hjU a ha) kbar p q hcard)
          (etaleModuleConstantComplex Λ kbar N))) =
      Nat.card (fixedSections (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
        (twistedGeometricFrobenius C.toOver (C.extendOver hjU a ha) kbar p q hcard)) •
          perfectDerivedTrace Λ ⟨_, hΓ⟩ (𝟙 _)) :
    perfectDerivedTrace Λ ⟨_, hY⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
            (openComplex Λ (Z := C.toOver) C.j f N)))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
              (openComplex Λ (Z := C.toOver) C.j f N)))
          (Y := (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
                (openComplex Λ (Z := C.toOver) C.j f N))))
          ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard) (ComplexShape.up ℤ)).app
            ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
              (openComplex Λ (Z := C.toOver) C.j f N)).obj) ≫
          (etaleModuleDirectImage.{u, 0} Λ
              (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
              ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.map
                (openDeck Λ (C.extendOver hjU a ha) C.j f a.hom ha
                  (C.isPullback_extend pU hjU a ha) N)))))) = 0 := by
  have : IsIntegralHom (Over.homMk (U := C.toOver) (V := Y) C.fb C.hq).left :=
    inferInstanceAs (IsIntegralHom C.fb)
  have hσ : C.extendOver hjU a ha ≫ Over.homMk (U := C.toOver) (V := Y) C.fb C.hq =
      Over.homMk (U := C.toOver) (V := Y) C.fb C.hq :=
    Over.OverMorphism.ext (C.extend_comp_fb pU hjU a.hom ha)
  exact (perfectDerivedTrace_openDeck_eq_twistedFrobenius Λ
    (Over.homMk (U := C.toOver) (V := Y) C.fb C.hq) (C.extendOver hjU a ha) hσ jU C.j f
    C.isPullback.flip a.hom ha (C.isPullback_extend pU hjU a ha) N kbar p q hcard hY hZ).trans
    (perfectDerivedTrace_twistedFrobenius_coverCompactification_eq_zero hjU C a ha kbar p q hcard
      Λ N hZ hp₂ hp₃ hΓ hweil)

end CoverStepEight

end Stacks.EtaleCohomology
