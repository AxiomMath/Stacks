module

public import Mathlib.CategoryTheory.Sites.Descent.Precoverage
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Effective

/-!
# Transport of effectivity of quasi-coherent descent data along a refinement

Let `𝒰 = {U i ⟶ S}` be a family of morphisms of schemes with fixed target and let `𝒱` refine it,
that is, let `Φ : 𝒱 ⟶ 𝒰` be a morphism of families over `𝟙 S` in the sense of Stacks 00VT (2).
Restriction of quasi-coherent descent data along `Φ` is
`AlgebraicGeometry.QuasicoherentDescentData.pullFunctor`, the functor of Stacks 023C.  This file
proves that an effective quasi-coherent descent datum for `𝒰` restricts to an effective one for
`𝒱`, and that conversely a datum for `𝒰` whose restriction to `𝒱` is effective is itself
effective as soon as the restriction functor is fully faithful.

It applies these to the refinement of a family by the one-element family given by the coproduct
`∐ U i ⟶ S` of its members.  For a finite jointly surjective family of flat morphisms from affine
schemes to an affine scheme — a standard fpqc covering, Stacks 022F — this one-element family is
itself an fpqc covering whose source is affine.

Both transports rest on a single isomorphism,
`AlgebraicGeometry.QuasicoherentDescentData.canonicalDescentFunctorCompPullFunctorIso`: the
canonical descent functor of a family, followed by restriction along a refinement, is the
canonical descent functor of the refinement.

The declarations below are in the namespace `AlgebraicGeometry.QuasicoherentDescentData`.

## Main definitions

* `canonicalDescentFunctorCompPullFunctorIso`: restricting the canonical descent datum of a
  quasi-coherent module along a refinement gives its canonical descent datum for the refining
  family, naturally in the module.
* `canonicalDescentFunctorCompPullFunctorIsoOver`: the same over an *arbitrary* morphism `g` of
  the targets, the canonical descent datum of the module being replaced on the right by that of
  its pullback along `g`.
* `toPushforward`, `ofPushforward` and `pullFunctorPushforwardCounitIso`: restriction along an
  isomorphism of the targets, and its inverse.
* `toSingletonFamily`: a family whose members factor through one morphism refines the one-element
  family of that morphism.
* `sigmaFamily` and `toSigmaFamily`: the one-element family given by the coproduct of a family,
  and the refinement of it by the family.

## Main results

* `isEffective_pullFunctor_obj` and `isEffective_of_iso_pullFunctor_obj`: effectivity passes to a
  refinement.
* `isEffective_of_isEffective_pullFunctor_obj`,
  `isEffective_of_isEffective_pullFunctor_obj_of_bijective` and
  `isEffective_pullFunctor_obj_iff`: effectivity descends from a refinement along a fully faithful
  restriction functor.
* `nonempty_fullyFaithful_pullFunctor_of_fullyFaithful` and
  `nonempty_fullyFaithful_pullFunctor_of_isPrestack`: sufficient conditions for that full
  faithfulness.
* `isEffective_pullFunctor_toSigmaFamily_obj`,
  `isEffective_of_isEffective_pullFunctor_toSigmaFamily_obj` and
  `isEffective_of_essSurj_pullFunctor_toSigmaFamily`: the same transports for the coproduct
  refinement.
* `presieve₀_sigmaFamily_mem_fpqcPrecoverage`: the one-element family given by the coproduct of a
  standard fpqc covering is an fpqc covering.
* `isEffective_pullFunctor_obj_over`: effectivity passes along a morphism of families over an
  arbitrary morphism of the targets, the quasi-coherent module on the base being replaced by its
  pullback.
* `isEffective_of_forall_isEffective_pushforward_of_iso`: effectivity transports along an
  isomorphism of the base.
* `essSurj_pullFunctor_toSigmaFamily_of_forall_isEffective` and
  `essSurj_pullFunctor_toSigmaFamily_iff`: once every quasi-coherent descent datum for the
  coproduct family is effective, essential surjectivity of restriction along the coproduct
  refinement is equivalent to effectivity of every quasi-coherent descent datum for the family.

## Implementation notes

The coproduct is formed in `Scheme.{u}`, so the index type of the family must be `Small.{u}`;
that is automatic for the finite index of a standard fpqc covering.

In `canonicalDescentFunctorCompPullFunctorIsoOver` the two spellings
`AlgebraicGeometry.Scheme.Modules.pullback g` and
`(AlgebraicGeometry.modulePullbackPseudofunctor.map g.op.toLoc).toFunctor` of the inverse image
are identified by `rfl`; at a concrete `g` the kernel does not finish that conversion, so `g` is
kept a variable there.

## References

* [Stacks Project, Tag 00VT](https://stacks.math.columbia.edu/tag/00VT)
* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
* [Stacks Project, Tag 023C](https://stacks.math.columbia.edu/tag/023C)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory Opposite

universe w' w u

namespace AlgebraicGeometry

namespace QuasicoherentDescentData

variable {S : Scheme.{u}} {𝒰 : PreZeroHypercover.{w} S} {𝒱 : PreZeroHypercover.{w'} S}

/-- Forgetting quasi-coherence turns the canonical descent functor of a family followed by
restriction along a morphism of families over a morphism `g` of the targets into
`ι ⋙ toDescentData ⋙ pullFunctor` for the pullback pseudofunctor. -/
private lemma canonical_comp_pullFunctor_comp_ι_over {U V : Scheme.{u}}
    {𝒲 : PreZeroHypercover.{w} V} {𝒳 : PreZeroHypercover.{w'} U} {g : U ⟶ V}
    (Φ : 𝒳.HomOver 𝒲 g) :
    (canonicalDescentFunctor 𝒲.f ⋙ pullFunctor Φ) ⋙ ObjectProperty.ι _ =
      (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι ⋙
        (modulePullbackPseudofunctor.toDescentData 𝒲.f ⋙
          Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
            (f := 𝒲.f) (p := g) (f' := 𝒳.f) (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀) := by
  rw [Functor.assoc, pullFunctor_comp_ι, ← Functor.assoc, canonicalDescentFunctor_comp_ι]
  exact Functor.assoc _ _ _

/-- The case `g = 𝟙 S` of `canonical_comp_pullFunctor_comp_ι_over`. -/
private lemma canonical_comp_pullFunctor_comp_ι (Φ : 𝒱.HomOver 𝒰 (𝟙 S)) :
    (canonicalDescentFunctor 𝒰.f ⋙ pullFunctor Φ) ⋙ ObjectProperty.ι _ =
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙
        (modulePullbackPseudofunctor.toDescentData 𝒰.f ⋙
          Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
            (f := 𝒰.f) (p := 𝟙 S) (f' := 𝒱.f) (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀) :=
  canonical_comp_pullFunctor_comp_ι_over Φ

/-- **The canonical descent datum of a module restricts to its canonical descent datum.**  For a
refinement `Φ : 𝒱 ⟶ 𝒰` over `𝟙 S`, restricting the canonical descent datum of a quasi-coherent
module on `S` relative to `𝒰` along `Φ` gives its canonical descent datum relative to `𝒱`,
naturally in the module. -/
noncomputable def canonicalDescentFunctorCompPullFunctorIso (Φ : 𝒱.HomOver 𝒰 (𝟙 S)) :
    canonicalDescentFunctor 𝒰.f ⋙ pullFunctor Φ ≅ canonicalDescentFunctor 𝒱.f := by
  exact Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (eqToIso (by exact canonical_comp_pullFunctor_comp_ι Φ) ≪≫
      Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι
        (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
            modulePullbackPseudofunctor Φ.w₀ ≪≫
          Functor.isoWhiskerRight
            (Cat.Hom.toNatIso (modulePullbackPseudofunctor.mapId (.mk (.op S)))) _ ≪≫
          Functor.leftUnitor _) ≪≫
      eqToIso (by exact (canonicalDescentFunctor_comp_ι 𝒱.f).symm))

/-- **Effectivity passes to a refinement.**  The restriction along a refinement of an effective
quasi-coherent descent datum is effective: it is the canonical datum of the same quasi-coherent
module on the base. -/
theorem isEffective_pullFunctor_obj (Φ : 𝒱.HomOver 𝒰 (𝟙 S))
    {D : QuasicoherentDescentData 𝒰.f} (hD : D.IsEffective) :
    ((pullFunctor Φ).obj D).IsEffective := by
  obtain ⟨M, ⟨e⟩⟩ := hD
  exact ⟨M, ⟨(canonicalDescentFunctorCompPullFunctorIso Φ).symm.app M ≪≫
    (pullFunctor Φ).mapIso e⟩⟩

/-- A quasi-coherent descent datum isomorphic to the restriction of an effective one along a
refinement is effective. -/
theorem isEffective_of_iso_pullFunctor_obj (Φ : 𝒱.HomOver 𝒰 (𝟙 S))
    {D₀ : QuasicoherentDescentData 𝒰.f} {D : QuasicoherentDescentData 𝒱.f}
    (hD₀ : D₀.IsEffective) (e : (pullFunctor Φ).obj D₀ ≅ D) : D.IsEffective :=
  ObjectProperty.prop_of_iso _ e (isEffective_pullFunctor_obj Φ hD₀)

/-- **Effectivity descends from a refinement.**  If restriction along the refinement `Φ` is fully
faithful, then a quasi-coherent descent datum whose restriction along `Φ` is effective is itself
effective. -/
theorem isEffective_of_isEffective_pullFunctor_obj (Φ : 𝒱.HomOver 𝒰 (𝟙 S))
    (hff : (pullFunctor Φ).FullyFaithful) {D : QuasicoherentDescentData 𝒰.f}
    (hD : ((pullFunctor Φ).obj D).IsEffective) : D.IsEffective := by
  obtain ⟨M, ⟨e⟩⟩ := hD
  exact ⟨M, ⟨hff.preimageIso ((canonicalDescentFunctorCompPullFunctorIso Φ).app M ≪≫ e)⟩⟩

/-- **Effectivity descends from a refinement.**  If restriction along the refinement `Φ` is
bijective on morphisms, then a quasi-coherent descent datum whose restriction along `Φ` is
effective is itself effective. -/
theorem isEffective_of_isEffective_pullFunctor_obj_of_bijective (Φ : 𝒱.HomOver 𝒰 (𝟙 S))
    (h : ∀ A B : QuasicoherentDescentData 𝒰.f,
      Function.Bijective ((pullFunctor Φ).map : (A ⟶ B) → _))
    {D : QuasicoherentDescentData 𝒰.f}
    (hD : ((pullFunctor Φ).obj D).IsEffective) : D.IsEffective :=
  isEffective_of_isEffective_pullFunctor_obj Φ
    ((Functor.FullyFaithful.nonempty_iff_map_bijective _).2 h).some hD

/-- Along a fully faithful restriction functor, a quasi-coherent descent datum is effective
exactly when its restriction along the refinement is. -/
theorem isEffective_pullFunctor_obj_iff (Φ : 𝒱.HomOver 𝒰 (𝟙 S))
    (hff : (pullFunctor Φ).FullyFaithful) {D : QuasicoherentDescentData 𝒰.f} :
    ((pullFunctor Φ).obj D).IsEffective ↔ D.IsEffective :=
  ⟨isEffective_of_isEffective_pullFunctor_obj Φ hff, isEffective_pullFunctor_obj Φ⟩

/-- **Full faithfulness of restriction on quasi-coherent descent data, from full faithfulness on
all descent data.**  If restriction along `Φ` is fully faithful on all descent data for the
pullback pseudofunctor, then it is fully faithful on quasi-coherent descent data. -/
theorem nonempty_fullyFaithful_pullFunctor_of_fullyFaithful (Φ : 𝒱.HomOver 𝒰 (𝟙 S))
    (h : (Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
      (f := 𝒰.f) (p := 𝟙 S) (f' := 𝒱.f) (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀).FullyFaithful) :
    Nonempty (pullFunctor Φ).FullyFaithful :=
  ⟨(((ObjectProperty.fullyFaithfulι _).comp h).ofIso
    (eqToIso (pullFunctor_comp_ι Φ).symm)).ofCompFaithful⟩

/-- **Full faithfulness of restriction along a covering refinement.**  If the pullback
pseudofunctor is a prestack for a topology `J` and the refining family generates a `J`-covering
sieve, then restriction along the refinement is fully faithful on quasi-coherent descent data. -/
theorem nonempty_fullyFaithful_pullFunctor_of_isPrestack {J : GrothendieckTopology Scheme.{u}}
    [modulePullbackPseudofunctor.IsPrestack J] (Φ : 𝒱.HomOver 𝒰 (𝟙 S))
    (h𝒱 : Sieve.ofArrows 𝒱.X 𝒱.f ∈ J S) : Nonempty (pullFunctor Φ).FullyFaithful :=
  nonempty_fullyFaithful_pullFunctor_of_fullyFaithful Φ
    (Pseudofunctor.DescentData.fullyFaithfulPullFunctor modulePullbackPseudofunctor
      (fun j ↦ by simpa using Φ.w₀ j) h𝒱)

section BaseChange

variable {U V : Scheme.{u}} {𝒲 : PreZeroHypercover.{w} V} {𝒳 : PreZeroHypercover.{w'} U}
  {g : U ⟶ V}

/-- **The canonical descent datum of a module restricts to the canonical descent datum of its
pullback.**  For a morphism of families `Φ : 𝒳 ⟶ 𝒲` over an *arbitrary* morphism `g : U ⟶ V` of
the targets, restricting the canonical descent datum of a quasi-coherent module on `V` relative
to `𝒲` along `Φ` gives the canonical descent datum of `g^* ` of that module relative to `𝒳`,
naturally in the module. -/
noncomputable def canonicalDescentFunctorCompPullFunctorIsoOver (Φ : 𝒳.HomOver 𝒲 g) :
    canonicalDescentFunctor 𝒲.f ⋙ pullFunctor Φ ≅
      Stacks.Modules.pullbackQcoh g ⋙ canonicalDescentFunctor 𝒳.f := by
  exact Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (eqToIso (by exact canonical_comp_pullFunctor_comp_ι_over Φ) ≪≫
      Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι
        (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
          modulePullbackPseudofunctor Φ.w₀) ≪≫
      eqToIso rfl)

/-- **Effectivity passes to a morphism of families over an arbitrary base morphism.**  The
restriction of an effective quasi-coherent descent datum along `Φ : 𝒳 ⟶ 𝒲` over `g : U ⟶ V` is
effective: it is the canonical datum of the pullback along `g` of the same quasi-coherent module
on `V`. -/
theorem isEffective_pullFunctor_obj_over (Φ : 𝒳.HomOver 𝒲 g)
    {D : QuasicoherentDescentData 𝒲.f} (hD : D.IsEffective) :
    ((pullFunctor Φ).obj D).IsEffective := by
  obtain ⟨M, ⟨eM⟩⟩ := hD
  exact ⟨(Stacks.Modules.pullbackQcoh g).obj M,
    ⟨(canonicalDescentFunctorCompPullFunctorIsoOver Φ).symm.app M ≪≫ (pullFunctor Φ).mapIso eM⟩⟩

end BaseChange

section BaseIso

variable {T T' : Scheme.{u}} (e : T ≅ T') (𝒲 : PreZeroHypercover.{w} T)

/-- The morphism of families from `𝒲` to its pushforward along an isomorphism of the target,
over that isomorphism: the index map and the component morphisms are identities. -/
def toPushforward : 𝒲.HomOver (𝒲.pushforward e.hom) e.hom where
  s₀ i := i
  h₀ _ := 𝟙 _
  w₀ _ := by simp [PreZeroHypercover.pushforward]

/-- The morphism of families back from the pushforward of `𝒲` along an isomorphism of the
target, over the inverse isomorphism. -/
def ofPushforward : (𝒲.pushforward e.hom).HomOver 𝒲 e.inv where
  s₀ i := i
  h₀ _ := 𝟙 _
  w₀ _ := by simp [PreZeroHypercover.pushforward]

/-- **Restricting along an isomorphism of targets and back is the identity.**  The two morphisms
of families `toPushforward` and `ofPushforward` induce mutually inverse restriction functors on
quasi-coherent descent data; this is the counit isomorphism. -/
noncomputable def pullFunctorPushforwardCounitIso (D : QuasicoherentDescentData 𝒲.f) :
    (pullFunctor (toPushforward e 𝒲)).obj ((pullFunctor (ofPushforward e 𝒲)).obj D) ≅ D :=
  ObjectProperty.isoMk
    (P := fun D : modulePullbackPseudofunctor.DescentData 𝒲.f ↦ ∀ i, (D.obj i).IsQuasicoherent)
    ((Pseudofunctor.DescentData.pullFunctorEquivalence modulePullbackPseudofunctor e
      (toPushforward e 𝒲).w₀ (ofPushforward e 𝒲).w₀).counitIso.app D.obj)

/-- **Effectivity transports along an isomorphism of the base.**  If every quasi-coherent descent
datum for the family `{X i ⟶ T ≅ T'}` pushed forward along an isomorphism `e : T ≅ T'` of the
targets is effective, then so is every quasi-coherent descent datum for the original family. -/
theorem isEffective_of_forall_isEffective_pushforward_of_iso
    (h : ∀ D' : QuasicoherentDescentData (𝒲.pushforward e.hom).f, D'.IsEffective)
    (D : QuasicoherentDescentData 𝒲.f) : D.IsEffective :=
  ObjectProperty.prop_of_iso _ (pullFunctorPushforwardCounitIso e 𝒲 D)
    (isEffective_pullFunctor_obj_over (toPushforward e 𝒲) (h _))

end BaseIso

section Coproduct

open Limits

variable {T : Scheme.{u}} (𝒱 : PreZeroHypercover.{w} T) [Small.{u} 𝒱.I₀]

/-- A family of morphisms with fixed target whose members factor through a single morphism
refines the one-element family of that morphism. -/
def toSingletonFamily {W : Scheme.{u}} (g : W ⟶ T) (h : ∀ i, 𝒱.X i ⟶ W)
    (hg : ∀ i, h i ≫ g = 𝒱.f i) :
    𝒱.HomOver (PreZeroHypercover.singleton.{0} g) (𝟙 T) where
  s₀ _ := PUnit.unit
  h₀ := h
  w₀ i := by rw [Category.comp_id]; exact hg i

/-- The one-element family whose member is the coproduct `∐ X i ⟶ T` of a family of morphisms
with fixed target `T`. -/
noncomputable abbrev sigmaFamily : PreZeroHypercover.{0} T :=
  PreZeroHypercover.singleton (Sigma.desc 𝒱.f)

/-- A family of morphisms with fixed target refines the one-element family given by the
coproduct of its members, by the inclusions of the summands. -/
noncomputable def toSigmaFamily : 𝒱.HomOver (sigmaFamily 𝒱) (𝟙 T) :=
  toSingletonFamily 𝒱 (Sigma.desc 𝒱.f) (fun i ↦ Sigma.ι 𝒱.X i) fun i ↦ Sigma.ι_desc 𝒱.f i

/-- **A standard fpqc covering collapses to a one-element fpqc covering.**  For a finite jointly
surjective family of flat morphisms from affine schemes to an affine scheme, Stacks 022F, the
one-element family given by the coproduct of its members is again an fpqc covering; its source is
affine, and its member is flat and surjective. -/
theorem presieve₀_sigmaFamily_mem_fpqcPrecoverage [IsAffine T] [Finite 𝒱.I₀]
    [∀ i, IsAffine (𝒱.X i)] [∀ i, Flat (𝒱.f i)]
    (hsurj : ⋃ i, Set.range (𝒱.f i) = Set.univ) :
    (sigmaFamily 𝒱).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T := by
  have : Surjective (Sigma.desc 𝒱.f) := Surjective.sigmaDesc_of_union_range_eq_univ hsurj
  rw [PreZeroHypercover.presieve₀_singleton]
  exact (Sigma.desc 𝒱.f).singleton_mem_fpqcPrecoverage

/-- **Effectivity for the coproduct passes to the family.**  An effective quasi-coherent descent
datum for the one-element family `∐ X i ⟶ T` restricts to an effective datum for the family. -/
theorem isEffective_pullFunctor_toSigmaFamily_obj
    {D : QuasicoherentDescentData (sigmaFamily 𝒱).f} (hD : D.IsEffective) :
    ((pullFunctor (toSigmaFamily 𝒱)).obj D).IsEffective :=
  isEffective_pullFunctor_obj _ hD

/-- **Effectivity for the family descends to the coproduct**, along a fully faithful restriction
functor. -/
theorem isEffective_of_isEffective_pullFunctor_toSigmaFamily_obj
    (hff : (pullFunctor (toSigmaFamily 𝒱)).FullyFaithful)
    {D : QuasicoherentDescentData (sigmaFamily 𝒱).f}
    (hD : ((pullFunctor (toSigmaFamily 𝒱)).obj D).IsEffective) : D.IsEffective :=
  isEffective_of_isEffective_pullFunctor_obj _ hff hD

/-- **The finite-to-one-element passage.**  If every quasi-coherent descent datum for the
one-element family `∐ X i ⟶ T` is effective, and every quasi-coherent descent datum for the
family is isomorphic to the restriction of one for that one-element family, then every
quasi-coherent descent datum for the family is effective. -/
theorem isEffective_of_essSurj_pullFunctor_toSigmaFamily
    [(pullFunctor (toSigmaFamily 𝒱)).EssSurj]
    (hsigma : ∀ D : QuasicoherentDescentData (sigmaFamily 𝒱).f, D.IsEffective)
    (D : QuasicoherentDescentData 𝒱.f) : D.IsEffective :=
  isEffective_of_iso_pullFunctor_obj _ (hsigma _)
    ((pullFunctor (toSigmaFamily 𝒱)).objObjPreimageIso D)

/-- If every quasi-coherent descent datum for a family is effective, then restriction along the
coproduct refinement is essentially surjective: an effective datum is the canonical datum of a
quasi-coherent module on the base, and the canonical datum for the coproduct family restricts to
it. -/
theorem essSurj_pullFunctor_toSigmaFamily_of_forall_isEffective
    (h : ∀ D : QuasicoherentDescentData 𝒱.f, D.IsEffective) :
    (pullFunctor (toSigmaFamily 𝒱)).EssSurj where
  mem_essImage D := by
    obtain ⟨M, ⟨eM⟩⟩ := h D
    exact ⟨(canonicalDescentFunctor (sigmaFamily 𝒱).f).obj M,
      ⟨(canonicalDescentFunctorCompPullFunctorIso (toSigmaFamily 𝒱)).app M ≪≫ eM⟩⟩

/-- Once every quasi-coherent descent datum for the one-element family `∐ X i ⟶ T` is effective,
the essential surjectivity of restriction along the coproduct refinement is equivalent to the
effectivity of every quasi-coherent descent datum for the family itself. -/
theorem essSurj_pullFunctor_toSigmaFamily_iff
    (hsigma : ∀ D : QuasicoherentDescentData (sigmaFamily 𝒱).f, D.IsEffective) :
    (pullFunctor (toSigmaFamily 𝒱)).EssSurj ↔
      ∀ D : QuasicoherentDescentData 𝒱.f, D.IsEffective :=
  ⟨fun _ ↦ isEffective_of_essSurj_pullFunctor_toSigmaFamily 𝒱 hsigma,
    essSurj_pullFunctor_toSigmaFamily_of_forall_isEffective 𝒱⟩

end Coproduct

end QuasicoherentDescentData

end AlgebraicGeometry

end
