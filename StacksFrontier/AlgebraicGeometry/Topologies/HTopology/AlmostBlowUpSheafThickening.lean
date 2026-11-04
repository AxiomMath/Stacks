module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.PrincipalCenterHDescent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Shrinking
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.EqualizerTransport

/-!
# Thickenings and the almost blowup conditions

The conditions of Stacks 0EVF on a presheaf `F` on the big h site over a scheme `S`, stated in
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion`, are that `F` be a
sheaf for the Zariski topology (1), that it satisfy the equalizer condition for a flat proper
surjective morphism of finite presentation onto an affine base (2), and that it send an almost
blowup square with affine base to a cartesian square of sets (3).

If a quasi-coherent ideal sheaf of finite type on a quasi-compact and quasi-separated scheme `X`
is supported on all of `X`, the empty scheme is the modification of an almost blowup square with
that centre. Under condition (1), condition (2) holds for every flat proper surjective morphism
of finite presentation of the site, with no affineness assumed of the target. Under conditions
(1) and (3), `F` restricts bijectively along every morphism of the site which is a thickening and
of finite presentation.

## Main results

* `AlgebraicGeometry.isAlmostBlowUpSquare_of_isEmpty_of_support_eq_univ`: an ideal sheaf of
  finite type supported everywhere has the empty scheme as the modification of an almost blowup
  square.
* `AlgebraicGeometry.BigHOver.subsingleton_of_isEmpty`: under condition (1) the sections over an
  object of the site with empty underlying scheme form a singleton.
* `AlgebraicGeometry.BigHOver.isSheafFor_singleton_of_flat`: condition (2) off the affine case.
* `AlgebraicGeometry.BigHOver.bijective_map_of_isThickening_of_isAffine`: under conditions (1)
  and (3), `F` restricts bijectively along a thickening of finite presentation with affine target.
* `AlgebraicGeometry.BigHOver.bijective_map_of_isThickening`: under conditions (1) and (3), `F`
  restricts bijectively along every thickening of finite presentation.

## References

* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EVE](https://stacks.math.columbia.edu/tag/0EVE)
* [Stacks Project, Tag 0EVA](https://stacks.math.columbia.edu/tag/0EVA)
* [Stacks Project, Tag 0EV8](https://stacks.math.columbia.edu/tag/0EV8)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/-- The ideal of sections supported on the whole space is the unit ideal sheaf. -/
private theorem supportedSectionsIdeal_univ (Y : Scheme.{u}) :
    supportedSectionsIdeal (Set.univ : Set Y) = ⊤ := by
  rw [supportedSectionsIdeal_eq_complementKernel (Set.univ : Set Y) isClosed_univ]
  have : IsEmpty (⟨(Set.univ : Set Y)ᶜ, isClosed_univ.isOpen_compl⟩ : Y.Opens) :=
    ⟨fun x => x.2 (Set.mem_univ _)⟩
  exact Scheme.ker_eq_top_of_isEmpty _

/-- A commuting square of schemes one of whose two outer corners is empty is cartesian. -/
private theorem isPullback_of_isEmpty {P A C D : Scheme.{u}} (fst : P ⟶ A) (snd : P ⟶ C)
    (f : A ⟶ D) (g : C ⟶ D) [IsEmpty C] : IsPullback fst snd f g := by
  have : IsEmpty P := Function.isEmpty snd.base
  have hinit : IsInitial P := isInitialOfIsEmpty
  have : IsEmpty ↥(Limits.pullback f g) :=
    Scheme.isEmpty_pullback f g (by simp [Set.range_eq_empty])
  exact IsPullback.of_iso_pullback ⟨hinit.hom_ext _ _⟩
    (asIso (hinit.to (Limits.pullback f g))) (hinit.hom_ext _ _) (hinit.hom_ext _ _)

/-- **An almost blowup square whose modification is empty.** Let `I` be a quasi-coherent ideal
sheaf of finite type on a quasi-compact and quasi-separated scheme `X` whose support is all of
`X`, so that the closed subscheme it cuts out is a thickening of `X`. Then every morphism from
the empty scheme to `X` is the modification of an almost blowup square with centre `I`. -/
public theorem isAlmostBlowUpSquare_of_isEmpty_of_support_eq_univ {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (I : X.IdealSheafData)
    (hI : I.IsFiniteType) (hsupp : (I.support : Set X) = Set.univ)
    (b : (∅ : Scheme.{u}) ⟶ X) : IsAlmostBlowUpSquare I b := by
  obtain ⟨X', b₀, h⟩ := exists_isAlmostBlowUpSquare X I hI
  have hsupp' : ((I.comap b₀).support : Set X') = Set.univ := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hsupp,
      Set.preimage_univ]
  have hle :
      (⊤ : X'.IdealSheafData) ≤ supportedSectionsIdeal ((I.comap b₀).support : Set X') := by
    rw [hsupp', supportedSectionsIdeal_univ]
  have hfp : FinitePresentation (⊤ : X'.IdealSheafData).subschemeι :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have key : IsAlmostBlowUpSquare I ((⊤ : X'.IdealSheafData).subschemeι ≫ b₀) :=
    (le_supportedSectionsIdeal_iff_isAlmostBlowUpSquare I b₀ h ⊤ hfp).1 hle
  have hb : b = Scheme.emptyTo _ ≫ (⊤ : X'.IdealSheafData).subschemeι ≫ b₀ :=
    Scheme.empty_ext _ _
  rw [hb]
  exact isAlmostBlowUpSquare_isIso_comp I key (Scheme.emptyTo _)

/-- A presheaf restricting bijectively along a morphism satisfies the sheaf condition for the
one-element family consisting of that morphism. -/
public theorem isSheafFor_singleton_of_bijective {C : Type*} [Category C] {G : Cᵒᵖ ⥤ Type*}
    {A A' : C} (i : A ⟶ A') (hi : Function.Bijective (G.map i.op)) :
    Presieve.IsSheafFor G (Presieve.singleton i) :=
  Presieve.isSheafFor_singleton.2 fun x _ => hi.existsUnique x

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-- A morphism property of schemes stable under base change passes from a morphism of the big h
category over `S` to its base change along an arbitrary morphism of the site. -/
private theorem map_pullback_snd_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {X Y Z : BigHOver B S hS} (f : Y ⟶ X) (g : Z ⟶ X)
    (hf : P ((BigHOver.toScheme B S hS).map f)) :
    P ((BigHOver.toScheme B S hS).map (Limits.pullback.snd f g)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((IsPullback.of_hasPullback f g).map (BigHOver.toScheme B S hS)) hf

/-- Finite presentation passes from a morphism of the big h category over `S` to its base change
along an arbitrary morphism of the site. -/
private theorem finitePresentation_map_pullback_snd {X Y Z : BigHOver B S hS} (f : Y ⟶ X)
    (g : Z ⟶ X) (hf : FinitePresentation ((BigHOver.toScheme B S hS).map f)) :
    FinitePresentation ((BigHOver.toScheme B S hS).map (Limits.pullback.snd f g)) :=
  ⟨map_pullback_snd_property B S hS @LocallyOfFinitePresentation f g
      hf.locallyOfFinitePresentation,
    map_pullback_snd_property B S hS @QuasiCompact f g hf.quasiCompact,
    map_pullback_snd_property B S hS @QuasiSeparated f g hf.quasiSeparated⟩

/-- Under condition (1), the sheaf condition for the one-element family of `f` follows from that
of the base changes of `f` along morphisms with affine source. -/
private theorem isSheafFor_singleton_of_affine_pullbacks
    (hZ : BigHOver.IsZariskiSheaf B S hS F) {X Y : BigHOver B S hS} (f : Y ⟶ X)
    (H : ∀ (W : BigHOver B S hS) (q : W ⟶ X),
      IsAffine ((BigHOver.toScheme B S hS).obj W) →
      Presieve.IsSheafFor F (Presieve.singleton (Limits.pullback.snd f q))) :
    Presieve.IsSheafFor F (Presieve.singleton f) := by
  rw [Presieve.isSheafFor_iff_generate]
  refine isSheafFor_of_affine_pullbacks hZ _ fun W q hW => ?_
  rw [← Sieve.pullbackArrows_comm, ← Presieve.isSheafFor_iff_generate,
    Presieve.pullback_singleton]
  exact H W q hW

/-- **The sections over an empty object are a singleton.** Let `F` satisfy condition (1) of
Stacks 0EVF, the sheaf condition for Zariski coverings, and let `X` be an object of the big h
category over `S` whose underlying scheme is empty. Then `F(X)` has exactly one element. -/
public theorem subsingleton_of_isEmpty (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (X : BigHOver B S hS) (hX : IsEmpty ((BigHOver.toScheme B S hS).obj X)) :
    Subsingleton (F.obj (op X)) ∧ Nonempty (F.obj (op X)) := by
  have hFor : Presieve.IsSheafFor F (⊥ : Presieve X) := by
    rw [← PreZeroHypercover.presieve₀_empty.{u + 1}]
    refine hZ X (PreZeroHypercover.empty.{u + 1} X) ?_
    have hbot : ((PreZeroHypercover.empty.{u + 1} X).map
        (BigHOver.toScheme B S hS)).presieve₀ = ⊥ := by
      simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map] using
        Presieve.ofArrows_of_isEmpty
          (fun i : (PreZeroHypercover.empty.{u + 1} X).I₀ =>
            (BigHOver.toScheme B S hS).map ((PreZeroHypercover.empty.{u + 1} X).f i))
    rw [hbot]
    have := hX
    exact Scheme.bot_mem_precoverage _ _
  have hcompat : (default : Presieve.FamilyOfElements F (⊥ : Presieve X)).Compatible :=
    fun _ _ _ _ _ _ _ h₁ _ _ => h₁.elim
  have hamalg : ∀ s : F.obj (op X),
      (default : Presieve.FamilyOfElements F (⊥ : Presieve X)).IsAmalgamation s :=
    fun _ _ _ h => h.elim
  obtain ⟨t, -, huniq⟩ := hFor default hcompat
  exact ⟨⟨fun a c => (huniq a (hamalg a)).trans (huniq c (hamalg c)).symm⟩, ⟨t⟩⟩

/-- **Condition (2) of Stacks 0EVF off the affine case.** Let `F` satisfy condition (1), the
sheaf condition for Zariski coverings, and condition (2), the sheaf condition for the one-element
family attached to a morphism of the site with affine target which is flat, proper, surjective
and of finite presentation. Then `F` satisfies the sheaf condition for the one-element family
attached to *any* morphism of the site which is flat, proper, surjective and of finite
presentation. -/
public theorem isSheafFor_singleton_of_flat (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (h2 : BigHOver.IsAffineFlatProperFinitePresentationSheaf B S hS F)
    {X Y : BigHOver B S hS} (f : Y ⟶ X)
    (hflat : Flat ((BigHOver.toScheme B S hS).map f))
    (hproper : IsProper ((BigHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map f))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map f)) :
    Presieve.IsSheafFor F (Presieve.singleton f) := by
  refine isSheafFor_singleton_of_affine_pullbacks B S hS F hZ f fun W q hW => ?_
  exact h2 W (Limits.pullback f q) (Limits.pullback.snd f q) hW
    (map_pullback_snd_property B S hS @Flat f q hflat)
    (map_pullback_snd_property B S hS @IsProper f q hproper)
    (map_pullback_snd_property B S hS @Surjective f q hsurj)
    (finitePresentation_map_pullback_snd B S hS f q hfp)

/-- Let `F` satisfy condition (1) of Stacks 0EVF, the sheaf condition for Zariski coverings, and
condition (3), the cartesianness of the image of an almost blowup square of the site with affine
base. Then `F` restricts bijectively along a morphism `g : T ⟶ T'` of the site whose target has
affine underlying scheme and which is a thickening and of finite presentation. -/
public theorem bijective_map_of_isThickening_of_isAffine
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (h3 : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F)
    {T T' : BigHOver B S hS} (g : T ⟶ T')
    (haff : IsAffine ((BigHOver.toScheme B S hS).obj T'))
    (hthick : Stacks.Thickenings.IsThickening ((BigHOver.toScheme B S hS).map g))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map g)) :
    Function.Bijective (F.map g.op) := by
  have := haff
  have hcl : IsClosedImmersion ((BigHOver.toScheme B S hS).map g) := hthick.1
  have hsurj : Surjective ((BigHOver.toScheme B S hS).map g) := ⟨hthick.2⟩
  have := hfp.locallyOfFinitePresentation
  have := hfp.quasiCompact
  have := hfp.quasiSeparated
  set I : ((BigHOver.toScheme B S hS).obj T').IdealSheafData :=
    ((BigHOver.toScheme B S hS).map g).ker with hIdef
  have heq : I.subschemeι =
      CategoryTheory.inv (((BigHOver.toScheme B S hS).map g).toImage) ≫
        (BigHOver.toScheme B S hS).map g :=
    (IsIso.eq_inv_comp ((BigHOver.toScheme B S hS).map g).toImage).mpr
      (Scheme.Hom.toImage_imageι _)
  have hIfp : FinitePresentation I.subschemeι := by
    rw [heq]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hIthick : Stacks.Thickenings.IsThickening I.subschemeι := by
    rw [heq]
    exact ⟨inferInstance, (inferInstance : Surjective _).1⟩
  have hIsupp : (I.support : Set ((BigHOver.toScheme B S hS).obj T')) = Set.univ := by
    rw [(Scheme.IdealSheafData.isThickening_subschemeι_iff I).mp hIthick]
    simp
  have hE : B.Contains (∅ : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion
      (Scheme.emptyTo ((BigHOver.toScheme B S hS).obj T)) T.left.2
  let O : B.Schemes := B.obj (∅ : Scheme.{u}) hE
  let a₀ : O ⟶ T.left := ObjectProperty.homMk (Scheme.emptyTo _)
  let N : BigHOver B S hS := Over.mk (a₀ ≫ T.hom)
  have hempty : IsEmpty (∅ : Scheme.{u}) := inferInstance
  have hNempty : IsEmpty ((BigHOver.toScheme B S hS).obj N) := hempty
  let e : N ⟶ T := Over.homMk a₀ rfl
  let b : N ⟶ T' := e ≫ g
  have hab : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b) :=
    isAlmostBlowUpSquare_of_isEmpty_of_support_eq_univ I
      ((Stacks.Flatness.finitePresentation_subschemeι_iff I).mp hIfp) hIsupp _
  have hcentre : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map g) ≅
      Over.mk I.subschemeι) :=
    ⟨Over.isoMk (asIso (((BigHOver.toScheme B S hS).map g).toImage))
      (Scheme.Hom.toImage_imageι _)⟩
  have hsq : IsPullback ((BigHOver.toScheme B S hS).map e)
      ((BigHOver.toScheme B S hS).map (𝟙 N)) ((BigHOver.toScheme B S hS).map g)
      ((BigHOver.toScheme B S hS).map b) :=
    @isPullback_of_isEmpty _ _ _ _ _ _ _ _ hNempty
  obtain ⟨hsub, hne⟩ := subsingleton_of_isEmpty B S hS F hZ N hNempty
  have := hsub
  have := hne
  exact (h3 T' N T N b g (𝟙 N) e I haff hab hcentre hsq).bijective_fst_of_subsingleton

/-- Let `F` satisfy condition (1) of Stacks 0EVF, the sheaf condition for Zariski coverings, and
condition (3), the cartesianness of the image of an almost blowup square of the site with affine
base. Then `F` restricts bijectively along every morphism of the site which is a thickening and
of finite presentation. -/
public theorem bijective_map_of_isThickening
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (h3 : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F)
    {T T' : BigHOver B S hS} (g : T ⟶ T')
    (hthick : Stacks.Thickenings.IsThickening ((BigHOver.toScheme B S hS).map g))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map g)) :
    Function.Bijective (F.map g.op) := by
  have hcl : IsClosedImmersion ((BigHOver.toScheme B S hS).map g) := hthick.1
  have : Mono g := (BigHOver.toScheme B S hS).mono_of_mono_map inferInstance
  have hFor : Presieve.IsSheafFor F (Presieve.singleton g) := by
    refine isSheafFor_singleton_of_affine_pullbacks B S hS F hZ g fun W q hW => ?_
    exact isSheafFor_singleton_of_bijective _ <| bijective_map_of_isThickening_of_isAffine B S hS F
      hZ h3 (Limits.pullback.snd g q) hW
      (map_pullback_snd_property B S hS @Stacks.Thickenings.IsThickening g q hthick)
      (finitePresentation_map_pullback_snd B S hS g q hfp)
  refine ⟨Presieve.isSeparatedFor_singleton.1 hFor.isSeparatedFor, fun x => ?_⟩
  rw [Presieve.isSheafFor_singleton] at hFor
  exact (hFor x fun p₁ p₂ h => by rw [(cancel_mono g).1 h]).exists

end BigHOver

end AlgebraicGeometry

end
