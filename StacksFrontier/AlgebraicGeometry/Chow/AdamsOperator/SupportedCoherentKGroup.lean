module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherent
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent modules on a closed subscheme and the K-group of modules supported on it

Let `i : Z ⟶ X` be a closed immersion with `X` locally Noetherian. Direct image carries a
coherent `𝒪_Z`-module to a coherent `𝒪_X`-module whose set-theoretic support lies in `Z`, and
the resulting functor `Coh(𝒪_Z) ⥤ Coh_Z(X)` is exact and fully faithful, so it induces a
homomorphism `K'_0(Z) = K_0(Coh(𝒪_Z)) → K_0(Coh_Z(X))` of Grothendieck groups.

## Main definitions

* `AlgebraicGeometry.coherentToSupportedCoherent` is the functor `Coh(𝒪_Z) ⥤ Coh_Z(X)`.
* `AlgebraicGeometry.coherentToSupportedCoherentKZeroHom` is the induced homomorphism
  `K_0(Coh(𝒪_Z)) → K_0(Coh_Z(X))`.

## Main results

* `AlgebraicGeometry.shortExact_map_coherentToSupportedCoherent`: exactness of the functor.
* `AlgebraicGeometry.fullyFaithfulCoherentToSupportedCoherent`: it is fully faithful.
* `AlgebraicGeometry.coherentToSupportedCoherentKZeroHom_mk` computes the homomorphism on the
  class of a coherent `𝒪_Z`-module: it is the class of its direct image.

## Implementation notes

The functor is a lift of `AlgebraicGeometry.Scheme.Modules.pushforward i` along two assertions:
coherence of `i_*ℱ`, which is [Stacks, Tag 087T]
(`AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion`), and the vanishing of the
stalks of `i_*ℱ` off the image of `i`, which is
`AlgebraicGeometry.notMem_supp_pushforward_of_notMemRange`. The lift is taken in two stages, so
that composing with either inclusion of a full subcategory returns the previous stage on the
nose.

Exactness is obtained by transporting a short exact sequence down to all `𝒪_X`-modules — through
the exact inclusion of coherent modules of [Stacks, Tag 01BY] and the exact direct image along a
closed immersion of [Stacks, Tag 08KS] — and then reflecting it back up along the inclusions of
the two weak Serre subcategories, which are exact and faithful, hence reflect exactness,
monomorphisms and epimorphisms.

Full faithfulness is full faithfulness of direct image along a closed immersion
(`Stacks.ClosedImmersion.fullyFaithfulPushforward`, [Stacks, Tag 08KS]) together with
faithfulness of the inclusion of a full subcategory. It does *not* make the functor an
equivalence: a coherent `𝒪_X`-module supported on `Z` need not be annihilated by the ideal sheaf
cutting out `Z`, and by [Stacks, Tag 087T] annihilation is exactly what the essential image of
direct image on coherent modules asks for.

## References

* [Stacks Project, Tag 0FDT](https://stacks.math.columbia.edu/tag/0FDT)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]

/-- The inclusion of a weak Serre subcategory reflects short exact sequences: it is exact, so it
reflects exactness of a short complex, and faithful, so it reflects monomorphisms and
epimorphisms. -/
private lemma shortExact_of_shortExact_map_ι {A : Type*} [Category A] [Abelian A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] {S : ShortComplex P.FullSubcategory}
    (hS : (S.map P.ι).ShortExact) : S.ShortExact := by
  have : PreservesFiniteLimits P.ι := P.preservesFiniteLimits_ι_of_isWeakSerreClass
  have : PreservesFiniteColimits P.ι := P.preservesFiniteColimits_ι_of_isWeakSerreClass
  have : P.ι.PreservesHomology := ⟨P.preservesKernels_ι, P.preservesCokernels_ι⟩
  exact ShortComplex.ShortExact.mk' ((S.exact_map_iff_of_faithful P.ι).mp hS.exact)
    (P.ι.mono_of_mono_map hS.mono_f) (P.ι.epi_of_epi_map hS.epi_g)

/-- Direct image along a closed immersion into a locally Noetherian scheme, as a functor from
coherent `𝒪_Z`-modules to coherent `𝒪_X`-modules. -/
def pushforwardCoherentModules :
    Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf ⥤
      Stacks.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ObjectProperty.lift _
    (ObjectProperty.ι (Stacks.SheafOfModules.coherentModules Z.ringCatSheaf) ⋙
      Scheme.Modules.pushforward i)
    fun F => by
      have : SheafOfModules.IsCoherent (F.obj : Z.Modules) :=
        CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
      exact CoherentAbelian.stacksIsCoherent_of_isCoherent
        (isCoherent_pushforward_of_isClosedImmersion i (F.obj : Z.Modules))

/-- Direct image along a closed immersion is fully faithful on coherent modules: it is fully
faithful on all modules by [Stacks, Tag 08KS], and the inclusion of a full subcategory is
faithful. -/
def fullyFaithfulPushforwardCoherentModules :
    (pushforwardCoherentModules i).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf))
    (show (pushforwardCoherentModules i ⋙
        ObjectProperty.ι
          (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)).FullyFaithful from
      (ObjectProperty.fullyFaithfulι _).comp (Stacks.ClosedImmersion.fullyFaithfulPushforward i))

instance full_pushforwardCoherentModules : (pushforwardCoherentModules i).Full :=
  (fullyFaithfulPushforwardCoherentModules i).full

instance faithful_pushforwardCoherentModules : (pushforwardCoherentModules i).Faithful :=
  (fullyFaithfulPushforwardCoherentModules i).faithful

/-- **The exact inclusion functor `Coh(𝒪_Z) ⥤ Coh_Z(X)` of [Stacks, Tag 0FDT].** The direct
image of a coherent `𝒪_Z`-module is coherent by [Stacks, Tag 087T] and its stalks vanish off the
image of `i`, so it is a coherent `𝒪_X`-module whose set-theoretic support lies in `Z`. -/
def coherentToSupportedCoherent :
    Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf ⥤ SupportedCoherentModules i :=
  ObjectProperty.lift _ (pushforwardCoherentModules i) fun F x hx => by
    by_contra hxr
    exact notMem_supp_pushforward_of_notMemRange i (F.obj : Z.Modules) x hxr hx

/-- **The functor `Coh(𝒪_Z) ⥤ Coh_Z(X)` of [Stacks, Tag 0FDT] is fully faithful.** Direct image
along a closed immersion is fully faithful on coherent modules, and the inclusion of the Serre
subcategory of coherent `𝒪_X`-modules supported on `Z` is faithful. -/
def fullyFaithfulCoherentToSupportedCoherent :
    (coherentToSupportedCoherent i).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := ObjectProperty.ι (supportedCoherentProperty i))
    (show (coherentToSupportedCoherent i ⋙
        ObjectProperty.ι (supportedCoherentProperty i)).FullyFaithful from
      fullyFaithfulPushforwardCoherentModules i)

instance full_coherentToSupportedCoherent : (coherentToSupportedCoherent i).Full :=
  (fullyFaithfulCoherentToSupportedCoherent i).full

instance faithful_coherentToSupportedCoherent : (coherentToSupportedCoherent i).Faithful :=
  (fullyFaithfulCoherentToSupportedCoherent i).faithful

/-- Direct image is exact on coherent modules: a short exact sequence of coherent
`𝒪_Z`-modules stays short exact in all `𝒪_Z`-modules, because the inclusion of coherent modules
is exact ([Stacks, Tag 01BY]); its direct image is short exact, because direct image along a
closed immersion is exact ([Stacks, Tag 08KS]); and the inclusion of the coherent modules on `X`
reflects short exactness. -/
theorem shortExact_map_pushforwardCoherentModules
    (S : ShortComplex (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf))
    (hS : S.ShortExact) : (S.map (pushforwardCoherentModules i)).ShortExact := by
  have : PreservesFiniteLimits
      (SheafOfModules.pushforward.{u} (Scheme.Hom.toRingCatSheafHom i)) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pushforward i))
  have : PreservesFiniteColimits
      (SheafOfModules.pushforward.{u} (Scheme.Hom.toRingCatSheafHom i)) :=
    Scheme.Modules.preservesFiniteColimits_pushforward_of_isClosedImmersion i
  have : (SheafOfModules.pushforward.{u}
      (Scheme.Hom.toRingCatSheafHom i)).PreservesZeroMorphisms :=
    inferInstanceAs ((Scheme.Modules.pushforward i).PreservesZeroMorphisms)
  have hS₁ : (S.map (ObjectProperty.ι
      (Stacks.SheafOfModules.coherentModules Z.ringCatSheaf))).ShortExact := hS.map_of_exact _
  have hS₂ : ((S.map (ObjectProperty.ι
      (Stacks.SheafOfModules.coherentModules Z.ringCatSheaf))).map
        (SheafOfModules.pushforward.{u}
          (Scheme.Hom.toRingCatSheafHom i))).ShortExact := hS₁.map_of_exact _
  exact shortExact_of_shortExact_map_ι
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf) hS₂

/-- **The functor `Coh(𝒪_Z) ⥤ Coh_Z(X)` of [Stacks, Tag 0FDT] is exact.** The direct image of a
short exact sequence of coherent `𝒪_Z`-modules is short exact, and the inclusion of the Serre
subcategory of coherent `𝒪_X`-modules supported on `Z` reflects short exactness. -/
theorem shortExact_map_coherentToSupportedCoherent
    (S : ShortComplex (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf))
    (hS : S.ShortExact) : (S.map (coherentToSupportedCoherent i)).ShortExact :=
  shortExact_of_shortExact_map_ι (supportedCoherentProperty i)
    (shortExact_map_pushforwardCoherentModules i S hS)

/-- **[Stacks, Tag 0FDT], the comparison homomorphism of K-groups.** Let `X` be a locally
Noetherian scheme and `Z ⊂ X` a closed subscheme. The exact inclusion functor
`Coh(𝒪_Z) ⥤ Coh_Z(X)` induces a homomorphism `K'_0(Z) = K_0(Coh(𝒪_Z)) → K_0(Coh_Z(X))` taking
the class of a coherent `𝒪_Z`-module to the class of its direct image. -/
@[stacks 0FDT "the exact fully faithful inclusion functor Coh(Z) → Coh_Z(X) and the \
homomorphism K'_0(Z) = K_0(Coh(Z)) → K_0(Coh_Z(X)) that it induces. That this homomorphism is \
an isomorphism is NOT covered: the source inverts it by sending a coherent module F supported \
on Z to the class of the graded module of its I-adic filtration. The graded pieces of that \
filtration are available, as the short exact sequence with the coherence and support bound of \
Stacks.AlgebraicGeometry.IdealAdicFiltration; what is missing is a comparison between the \
support and coherence predicates used there and those defining SupportedCoherentModules, and \
the local finiteness of the filtration over a merely locally Noetherian scheme, the available \
finiteness input being quasi-compact"]
def coherentToSupportedCoherentKZeroHom :
    KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) →+
      KZero (SupportedCoherentModules i) :=
  KZero.lift (fun F => KZero.mk _ ((coherentToSupportedCoherent i).obj F))
    fun S hS => KZero.mk_of_shortExact _ (shortExact_map_coherentToSupportedCoherent i S hS)

/-- **[Stacks, Tag 0FDT].** The comparison homomorphism `K_0(Coh(𝒪_Z)) → K_0(Coh_Z(X))` takes
the class of a coherent `𝒪_Z`-module `ℱ` to the class of its direct image `i_*ℱ`. -/
@[simp, stacks 0FDT "the defining property of the comparison homomorphism"]
theorem coherentToSupportedCoherentKZeroHom_mk
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    coherentToSupportedCoherentKZeroHom i (KZero.mk _ F) =
      KZero.mk _ ((coherentToSupportedCoherent i).obj F) :=
  KZero.lift_mk _ _ _

end AlgebraicGeometry

end
