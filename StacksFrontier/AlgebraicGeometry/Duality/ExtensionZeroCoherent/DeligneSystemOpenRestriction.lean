module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemExistence
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictFunctorOpensRange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing

/-!
# Restricting Deligne systems along open immersions

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `f : Y ⟶ X` be an open
immersion, with `Y` Noetherian. If `j' : U' ⟶ Y` is an open immersion whose image is
`f⁻¹(j(U))` — for instance the restriction `j ∣_ W : U ∩ W ⟶ W` of `j` to an open `W` of `X` —
then the restriction along `f` of a Deligne system `(𝓘^n𝓕^•)` for `j` is the Deligne system
`((𝓘|_Y)^n (𝓕^•|_Y))` for `j'`. This is the observation, used in the proof of
[Stacks, Tag 0G4T], that "it follows immediately from the construction of Deligne systems that
restrictions to opens preserves them".

The content is the identification `(𝓘^n𝓕^i)|_Y = (𝓘|_Y)^n(𝓕^i|_Y)` of subsheaves,
`Stacks.Algebraization.isIso_idealPowerMultipleRestrictMap`, for the coherent, hence
quasi-coherent, terms of `𝓕^•`; the ideal `𝓘|_Y` cuts out `f⁻¹(X ∖ U) = Y ∖ U'`.

## Main definitions

* `AlgebraicGeometry.restrictFunctorMapDerivedCategoryCompIso` and
  `AlgebraicGeometry.restrictBoundedCoherentLiftCompIso`: restriction along a composite of open
  immersions is the composite of the restrictions, on `D(𝒪)` and on `D^b_{Coh}`.
* `AlgebraicGeometry.restrictBoundedCoherentLiftIdIso`: restriction along the identity.
* `AlgebraicGeometry.DeligneSystem.restrict`: the restriction of a Deligne system along an open
  immersion.
* `AlgebraicGeometry.DeligneSystem.restrictSystemIso`: its system is the restriction of the
  system.

## Main results

* `AlgebraicGeometry.ProIsoDeligneSystem.restrict`: an inverse system pro-isomorphic to a Deligne
  system restricts, along an open immersion, to one pro-isomorphic to a Deligne system.

## References

* [Stacks Project, Tag 0G4T](https://stacks.math.columbia.edu/tag/0G4T)
* [Stacks Project, Tag 0G2G](https://stacks.math.columbia.edu/tag/0G2G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.IdealPower

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-! ### Restriction along composites of open immersions -/

section Comp

/-- Restriction along a composite `h = f ≫ g` of open immersions is restriction along `g` followed
by restriction along `f`, on unbounded derived categories. -/
public def restrictFunctorMapDerivedCategoryCompIso (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h] (hfg : f ≫ g = h) :
    (Scheme.Modules.restrictFunctor h).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor g).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor f).mapDerivedCategory :=
  letI : PreservesFiniteLimits (Scheme.Modules.restrictFunctor g ⋙
      Scheme.Modules.restrictFunctor f) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (Scheme.Modules.restrictFunctor g ⋙
      Scheme.Modules.restrictFunctor f) := comp_preservesFiniteColimits _ _
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (Scheme.Modules.restrictFunctorCongr hfg.symm ≪≫
        Scheme.Modules.restrictFunctorComp f g) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

/-- Restriction along a composite `h = f ≫ g` of open immersions is restriction along `g` followed
by restriction along `f`, as functors `D^b_{Coh}(𝒪_Z) ⥤ D^b_{Coh}(𝒪_X)`. -/
public def restrictBoundedCoherentLiftCompIso [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h] (hfg : f ≫ g = h) :
    restrictBoundedCoherentLift h ≅
      restrictBoundedCoherentLift g ⋙ restrictBoundedCoherentLift f :=
  NatIso.ofComponents
    (fun K => (boundedCoherentDerived X).fullyFaithfulι.preimageIso
      ((restrictFunctorMapDerivedCategoryCompIso f g h hfg).app K.obj))
    (fun {K L} φ => (boundedCoherentDerived X).ι.map_injective (by simp))

/-- Restriction along the identity is the identity, as a functor of `D^b_{Coh}(𝒪_X)`. -/
public def restrictBoundedCoherentLiftIdIso [IsLocallyNoetherian X] :
    restrictBoundedCoherentLift (𝟙 X) ≅ 𝟭 (BoundedCoherentDerived X) :=
  letI e : (Scheme.Modules.restrictFunctor (𝟙 X)).mapDerivedCategory ≅
      𝟭 (DerivedCategory X.Modules) :=
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        Scheme.Modules.restrictFunctorId ≪≫
      CategoryTheory.Functor.mapDerivedCategoryId _
  NatIso.ofComponents
    (fun K => (boundedCoherentDerived X).fullyFaithfulι.preimageIso (e.app K.obj))
    (fun {K L} φ => (boundedCoherentDerived X).ι.map_injective (by simp))

end Comp

/-! ### The ideal-power subcomplexes restrict to the ideal-power subcomplexes -/

section IdealPower

variable (f : Y ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)

/-- The restricted complex `𝓕^•|_Y`. -/
public abbrev restrictComplex (F : CochainComplex X.Modules ℤ) : CochainComplex Y.Modules ℤ :=
  ((Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- The comparison `(𝓘^n M)|_Y ⟶ (𝓘|_Y)^n (M|_Y)` composed with the inclusion of the target into
`M|_Y` is the restriction of the inclusion of `𝓘^n M` into `M`. -/
public lemma idealPowerMultipleRestrictMap_comp_ι (n : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] :
    Stacks.Algebraization.idealPowerMultipleRestrictMap f I n M ≫
        (idealPowerMultiple (I.comap f) n ((Scheme.Modules.restrictFunctor f).obj M)).ι =
      (Scheme.Modules.restrictFunctor f).map (idealPowerMultiple I n M).ι :=
  SheafOfModules.hom_ext (PresheafOfModules.Hom.ext (funext fun W => ModuleCat.Hom.ext
    (LinearMap.ext fun x =>
      Stacks.Algebraization.idealPowerMultipleRestrictMap_app_coe f I n M W.unop x)))

/-- A morphism into a term of `(𝓘|_Y)^n(𝓕^•|_Y)` is determined by its composite with the
inclusion into `𝓕^•|_Y`. -/
public lemma cancel_idealPowerComplexSystem_inclusion {G : CochainComplex Y.Modules ℤ}
    (J : Y.IdealSheafData) (n : ℕ) (i : ℤ) {A : Y.Modules}
    (a b : A ⟶ ((idealPowerComplexSystem J G).complex n).X i)
    (h : a ≫ ((idealPowerComplexSystem J G).inclusion n).f i =
      b ≫ ((idealPowerComplexSystem J G).inclusion n).f i) : a = b :=
  cancel_sheafSubmodule_ι (idealPowerMultiple J n (G.X i)) a b h

variable {F : CochainComplex X.Modules ℤ} (S : IdealPowerComplexSystem I F)

/-- A morphism into `(𝓘|_Y)^n(𝓕^•|_Y)` is determined by its composite with the inclusion into
`𝓕^•|_Y`. -/
public lemma cancel_idealPowerComplexSystem_inclusion_complex {G : CochainComplex Y.Modules ℤ}
    (J : Y.IdealSheafData) (n : ℕ) {A : CochainComplex Y.Modules ℤ}
    (a b : A ⟶ (idealPowerComplexSystem J G).complex n)
    (h : a ≫ (idealPowerComplexSystem J G).inclusion n =
      b ≫ (idealPowerComplexSystem J G).inclusion n) : a = b := by
  ext i : 1
  apply cancel_idealPowerComplexSystem_inclusion J n i
  have h' := congrArg (fun z => HomologicalComplex.Hom.f z i) h
  simpa only [HomologicalComplex.comp_f] using h'

/-- Degreewise, the restriction of `𝓘^n𝓕^•` is `(𝓘|_Y)^n(𝓕^•|_Y)`. -/
public def restrictIdealPowerTermIso (hF : ∀ i, (F.X i).IsQuasicoherent) (n : ℕ) (i : ℤ) :
    (Scheme.Modules.restrictFunctor f).obj ((S.complex n).X i) ≅
      ((idealPowerComplexSystem (I.comap f) (restrictComplex f F)).complex n).X i :=
  haveI : (F.X i).IsQuasicoherent := hF i
  (Scheme.Modules.restrictFunctor f).mapIso (S.termIso n i) ≪≫
    @asIso _ _ _ _ (Stacks.Algebraization.idealPowerMultipleRestrictMap f I n (F.X i))
      (Stacks.Algebraization.isIso_idealPowerMultipleRestrictMap f I n (F.X i))

/-- The degreewise identification is compatible with the inclusions into `𝓕^•|_Y`. -/
public lemma restrictIdealPowerTermIso_hom_comp_inclusion (hF : ∀ i, (F.X i).IsQuasicoherent)
    (n : ℕ) (i : ℤ) :
    (restrictIdealPowerTermIso f I S hF n i).hom ≫
        ((idealPowerComplexSystem (I.comap f) (restrictComplex f F)).inclusion n).f i =
      (Scheme.Modules.restrictFunctor f).map ((S.inclusion n).f i) := by
  have : (F.X i).IsQuasicoherent := hF i
  exact (Category.assoc _ _ _).trans
    ((congrArg ((Scheme.Modules.restrictFunctor f).map (S.termIso n i).hom ≫ ·)
      (idealPowerMultipleRestrictMap_comp_ι f I n (F.X i))).trans
      ((Functor.map_comp _ _ _).symm.trans (congrArg _ (S.include_f n i))))

/-- The restriction of the complex `𝓘^n𝓕^•` is the complex `(𝓘|_Y)^n(𝓕^•|_Y)`. -/
public def restrictIdealPowerComplexIso (hF : ∀ i, (F.X i).IsQuasicoherent) (n : ℕ) :
    ((Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (S.complex n) ≅
      (idealPowerComplexSystem (I.comap f) (restrictComplex f F)).complex n :=
  HomologicalComplex.Hom.isoOfComponents (fun i => restrictIdealPowerTermIso f I S hF n i)
    (fun i j _ => by
      apply cancel_idealPowerComplexSystem_inclusion
      rw [Category.assoc, ← ((idealPowerComplexSystem (I.comap f)
          (restrictComplex f F)).inclusion n).comm i j,
        ← Category.assoc, restrictIdealPowerTermIso_hom_comp_inclusion, Category.assoc,
        restrictIdealPowerTermIso_hom_comp_inclusion]
      change (Scheme.Modules.restrictFunctor f).map ((S.inclusion n).f i) ≫
          (Scheme.Modules.restrictFunctor f).map (F.d i j) =
        (Scheme.Modules.restrictFunctor f).map ((S.complex n).d i j) ≫
          (Scheme.Modules.restrictFunctor f).map ((S.inclusion n).f j)
      rw [← Functor.map_comp, ← Functor.map_comp, (S.inclusion n).comm i j])

/-- The identifications of `restrictIdealPowerComplexIso` are compatible with the inclusions. -/
public lemma restrictIdealPowerComplexIso_hom_comp_inclusion
    (hF : ∀ i, (F.X i).IsQuasicoherent) (n : ℕ) :
    (restrictIdealPowerComplexIso f I S hF n).hom ≫
        (idealPowerComplexSystem (I.comap f) (restrictComplex f F)).inclusion n =
      ((Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (S.inclusion n) := by
  ext i : 1
  exact restrictIdealPowerTermIso_hom_comp_inclusion f I S hF n i

/-- The restriction of the system `(𝓘^n𝓕^•)` of complexes is the system `((𝓘|_Y)^n(𝓕^•|_Y))`. -/
public def restrictIdealPowerSystemIso (hF : ∀ i, (F.X i).IsQuasicoherent) :
    Functor.ofOpSequence S.transition ⋙
        (Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Functor.ofOpSequence (idealPowerComplexSystem (I.comap f) (restrictComplex f F)).transition :=
  let α : Functor.ofOpSequence S.transition ⋙
        (Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      Functor.ofOpSequence
        (idealPowerComplexSystem (I.comap f) (restrictComplex f F)).transition :=
    NatTrans.ofOpSequence (fun n => (restrictIdealPowerComplexIso f I S hF n).hom) (fun n => by
      rw [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply cancel_idealPowerComplexSystem_inclusion_complex
      have h₁ : ((restrictIdealPowerComplexIso f I S hF (n + 1)).hom ≫
            (idealPowerComplexSystem (I.comap f) (restrictComplex f F)).transition n) ≫
          (idealPowerComplexSystem (I.comap f) (restrictComplex f F)).inclusion n =
          ((Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (S.inclusion (n + 1)) :=
        (Category.assoc _ _ _).trans
          ((congrArg ((restrictIdealPowerComplexIso f I S hF (n + 1)).hom ≫ ·)
            ((idealPowerComplexSystem (I.comap f) (restrictComplex f F)).transition_include
              n)).trans (restrictIdealPowerComplexIso_hom_comp_inclusion f I S hF (n + 1)))
      have h₂ : (((Scheme.Modules.restrictFunctor f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (S.transition n) ≫
            (restrictIdealPowerComplexIso f I S hF n).hom) ≫
          (idealPowerComplexSystem (I.comap f) (restrictComplex f F)).inclusion n =
          ((Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (S.inclusion (n + 1)) :=
        (Category.assoc _ _ _).trans
          ((congrArg (((Scheme.Modules.restrictFunctor f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (S.transition n) ≫ ·)
            (restrictIdealPowerComplexIso_hom_comp_inclusion f I S hF n)).trans
            ((Functor.map_comp _ _ _).symm.trans (congrArg _ (S.transition_include n))))
      exact h₂.trans h₁.symm)
  haveI : ∀ n, IsIso (α.app n) := fun n => (restrictIdealPowerComplexIso f I S hF n.unop).isIso_hom
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  asIso α

end IdealPower

/-! ### The restriction of a Deligne system -/

namespace DeligneSystem

variable {U U' : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]
  (D : DeligneSystem j) (f : Y ⟶ X) [IsOpenImmersion f] [IsNoetherian Y]
  (j' : U' ⟶ Y) [IsOpenImmersion j']
  (hj : Set.range j'.base = f.base ⁻¹' Set.range j.base)

omit [IsOpenImmersion f] [IsNoetherian Y] [IsOpenImmersion j'] in
include hj in
/-- The restricted ideal cuts out the complement of `U'`. -/
public lemma support_comap_idealSheaf :
    ((D.idealSheaf.comap f).support : Set Y) = (Set.range j'.base)ᶜ := by
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    D.support_idealSheaf, hj, Set.preimage_compl]

omit [IsNoetherian Y] in
/-- The terms of the restricted complex are coherent. -/
public lemma isCoherent_restrictComplex (i : ℤ) : ((restrictComplex f D.complex).X i).IsCoherent :=
  have := D.isCoherent_complex i
  Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion f (D.complex.X i)

omit [IsNoetherian Y] in
/-- The restricted complex is bounded below. -/
public lemma exists_isStrictlyGE_restrictComplex :
    ∃ a : ℤ, (restrictComplex f D.complex).IsStrictlyGE a := by
  obtain ⟨a, ha⟩ := D.exists_isStrictlyGE
  refine ⟨a, (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => ?_⟩
  exact (Scheme.Modules.restrictFunctor f).map_isZero (D.complex.isZero_of_isStrictlyGE a i hi)

omit [IsNoetherian Y] in
/-- The restricted complex is bounded above. -/
public lemma exists_isStrictlyLE_restrictComplex :
    ∃ b : ℤ, (restrictComplex f D.complex).IsStrictlyLE b := by
  obtain ⟨b, hb⟩ := D.exists_isStrictlyLE
  refine ⟨b, (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => ?_⟩
  exact (Scheme.Modules.restrictFunctor f).map_isZero (D.complex.isZero_of_isStrictlyLE b i hi)

/-- **The restriction of a Deligne system along an open immersion.** For a Deligne system
`(𝓘^n𝓕^•)` along `j : U ⟶ X`, an open immersion `f : Y ⟶ X` and an open immersion
`j' : U' ⟶ Y` with image `f⁻¹(j(U))`, it is the Deligne system `((𝓘|_Y)^n(𝓕^•|_Y))` along
`j'`. -/
public def restrict : DeligneSystem j' :=
  DeligneTriangle.deligneSystemOfComplex j' (D.idealSheaf.comap f)
    (D.support_comap_idealSheaf f j' hj) (restrictComplex f D.complex)
    (D.exists_isStrictlyGE_restrictComplex f) (D.exists_isStrictlyLE_restrictComplex f)
    (D.isCoherent_restrictComplex f)

/-- **The system of the restriction of a Deligne system is the restriction of its system.** -/
public def restrictSystemIso :
    (D.restrict f j' hj).system ≅ D.system ⋙ restrictBoundedCoherentLift f :=
  (Functor.FullyFaithful.whiskeringRight (boundedCoherentDerived Y).fullyFaithfulι
      ℕᵒᵖ).preimageIso
    (Functor.isoWhiskerRight (restrictIdealPowerSystemIso f D.idealSheaf D.powers
          (fun i => haveI := D.isCoherent_complex i; isQuasicoherent_of_isCoherent _)).symm
        DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Scheme.Modules.restrictFunctor f).mapDerivedCategoryFactors.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight D.representation.symm _ ≪≫
      Functor.associator _ _ _)

end DeligneSystem

/-! ### Being pro-isomorphic to a Deligne system -/

namespace ProIsoDeligneSystem

variable {U U' : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]

/-- **An inverse system pro-isomorphic to a Deligne system restricts to one.** If `(K_n)` is
pro-isomorphic to a Deligne system along `j : U ⟶ X`, `f : Y ⟶ X` is an open immersion and
`j' : U' ⟶ Y` an open immersion with image `f⁻¹(j(U))`, then `(K_n|_Y)` is pro-isomorphic to a
Deligne system along `j'`, namely to the restriction of the given one. -/
public lemma restrict {F : ℕᵒᵖ ⥤ BoundedCoherentDerived X} (h : ProIsoDeligneSystem j F)
    (f : Y ⟶ X) [IsOpenImmersion f] [IsNoetherian Y] (j' : U' ⟶ Y) [IsOpenImmersion j']
    (hj : Set.range j'.base = f.base ⁻¹' Set.range j.base) :
    ProIsoDeligneSystem j' (F ⋙ restrictBoundedCoherentLift f) := by
  obtain ⟨D, ⟨i⟩⟩ := h
  refine ⟨D.restrict f j' hj, ⟨?_⟩⟩
  exact ProSeq.isoOfProIso (Pro.proIsoWhiskerRight (ProSeq.proIsoOfIso i) _) ≪≫
    ProSeq.ofIsoOfNatIso (D.restrictSystemIso f j' hj).symm

end ProIsoDeligneSystem

end AlgebraicGeometry

end
