module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.RingedSpaceComorphism
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.PointClosureSquare
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforward.OpenImmersionClosure

/-!
# Direct images along a closed immersion preserve coherence

Let `i : Z ⟶ X` be a closed immersion of schemes with `X` locally Noetherian, and let `G` be a
coherent `𝒪_Z`-module. This file proves that `i_* G` is a coherent `𝒪_X`-module, and deduces
the implication of [Stacks, Tag 0BK2] complementary to the forward implication: around
the square of point closures of an open immersion, coherence of the direct image to the closure
of `{j x}` forces coherence of the iterated direct image to `X`.

The argument is the one indicated by the source. On a locally Noetherian scheme a quasi-coherent
module of finite type is coherent
(`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`), and
quasi-coherence of `i_* G` is [Stacks, Tag 01LC] because a closed immersion is quasi-compact and
quasi-separated. So everything is in the finite type of `i_* G`, which is checked on the affine
opens `V` of `X`: there `G` restricted to `i ⁻¹ᵁ V` has *finitely many global* generating
sections, because a coherent module on an affine open is the sheaf associated with a finite
module, and those sections push forward.

## Main results

* `Stacks.ClosedImmersion.epi_pushforwardUnitHom`: the comparison `𝒪_X ⟶ i_* 𝒪_Z` of a closed
  immersion is an epimorphism of `𝒪_X`-modules.
* `Stacks.ClosedImmersion.generatingSectionsPushforward`: global generating sections push
  forward along a closed immersion, with the same index type.
* `Stacks.ClosedImmersion.isFiniteType_pushforward_of_isCoherent`: the direct image of a
  coherent module along a closed immersion is of finite type.
* `Stacks.ClosedImmersion.isCoherent_pushforward`: **the direct image of a coherent module along
  a closed immersion of a locally Noetherian scheme is coherent.**
* `Stacks.LocalCohomology.isCoherent_pushforward_pointClosure_of_isCoherent_pushforward`: the
  reverse implication of the coherence equivalence of [Stacks, Tag 0BK2].

## Implementation notes

Two generic steps are isolated because nothing in the library had them.

`epi_pushforwardUnitHom` is the only place where the geometry of a closed immersion enters: it
says that `𝒪_X ⟶ i_* 𝒪_Z` is an epimorphism. Epimorphisms of sheaves of modules are the locally
surjective morphisms (`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective`), and
`SheafOfModules.unitToPushforwardObjUnit` is, on sections, the comorphism of `i` read through
the forgetful functor to abelian groups, so local surjectivity of the comorphism as a morphism of
sheaves of rings — which is `Stacks.ClosedImmersion.isLocallySurjective_c_toShHom` — is literally
the condition to be verified, with the same image sieves.

`epi_mapFree` says that `Mathlib`'s `SheafOfModules.mapFree`, the comparison
`free I ⟶ F.obj (free I)` induced by a morphism `unit S ⟶ F.obj (unit R)`, is an epimorphism as
soon as that morphism is one and `F` preserves `I`-indexed coproducts. `Mathlib`'s
`SheafOfModules.GeneratingSections.map` and the library's
`Stacks.SheafOfModules.LocalCokernel.mapFiniteGeneratingSections` both transport generating
sections along a functor, but both ask for `unit S ≅ F.obj (unit R)` to be an *isomorphism*,
which it is not for a closed immersion; the coproduct of copies of a mere epimorphism is still an
epimorphism, which is all that is needed, and that is what `epi_mapFree` records. Its proof uses
no coproduct-of-epimorphisms lemma: the legs `F.map (ιFree j)` of the preserved colimit cocone
are jointly epic, and `SheafOfModules.ιFree_mapFree` identifies each composite with `η` followed
by a leg.

The `I`-indexed coproducts of a finite `I` are preserved because `Scheme.Modules.pushforward` is
additive; no right-exactness is needed for that step, only for `PreservesEpimorphisms`, which is
`Stacks.ClosedImmersion.preservesEpimorphisms_modulePushforward_of_isClosedImmersion` restated at
the scheme-level spelling of the functor.

`Z` is assumed locally Noetherian wherever that is needed rather than deduced from `X`: nothing
in the library derives `IsLocallyNoetherian Z` from a closed immersion into a locally Noetherian
scheme, and
`Stacks.LocalCohomology.isCoherent_of_isCoherent_pushforward` makes the same assumption. The
coherence result itself does not need it.

## References

* [Stacks Project, Tag 0BK2](https://stacks.math.columbia.edu/tag/0BK2)
* [Stacks Project, Tag 01QO](https://stacks.math.columbia.edu/tag/01QO)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v₁ v₂ u₁ u₂ u

namespace Stacks.ClosedImmersion

/-! ### The comparison `𝒪_X ⟶ i_* 𝒪_Z` of a closed immersion -/

section Unit

variable {Z X : Scheme.{u}}

/-- The canonical comparison `𝒪_X ⟶ i_* 𝒪_Z` of `𝒪_X`-modules attached to a morphism of
schemes: `Mathlib`'s `SheafOfModules.unitToPushforwardObjUnit`, at the morphism of sheaves of
rings underlying a morphism of schemes. -/
noncomputable def pushforwardUnitHom (i : Z ⟶ X) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

/-- On sections, `pushforwardUnitHom i` is the comorphism of `i`. -/
theorem pushforwardUnitHom_val_app_apply (i : Z ⟶ X) {U : (Opens X)ᵒᵖ}
    (a : X.ringCatSheaf.obj.obj U) :
    (pushforwardUnitHom i).val.app U a = i.toRingCatSheafHom.hom.app U a :=
  rfl

/-- **The comparison `𝒪_X ⟶ i_* 𝒪_Z` of a closed immersion is an epimorphism.** The comorphism
of a closed immersion is a locally surjective morphism of sheaves of rings
(`Stacks.ClosedImmersion.isLocallySurjective_c_toShHom`), and `pushforwardUnitHom` has the same
sections and hence the same image sieves, so it is locally surjective as a morphism of sheaves of
modules; epimorphisms of sheaves of modules are exactly the locally surjective morphisms. -/
instance epi_pushforwardUnitHom (i : Z ⟶ X) [IsClosedImmersion i] :
    Epi (pushforwardUnitHom i) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun s x hx => ?_⟩
  exact (isLocallySurjective_c_toShHom i).imageSieve_mem s x hx

/-- Pushforward of sheaves of modules along a closed immersion of schemes preserves
epimorphisms. This restates
`Stacks.ClosedImmersion.preservesEpimorphisms_modulePushforward_of_isClosedImmersion` at the
scheme-level spelling of the functor, so that instance search finds it for
`AlgebraicGeometry.Scheme.Modules.pushforward`. -/
instance preservesEpimorphisms_pushforward (i : Z ⟶ X) [IsClosedImmersion i] :
    (Scheme.Modules.pushforward i).PreservesEpimorphisms :=
  preservesEpimorphisms_modulePushforward_of_isClosedImmersion i

end Unit

/-- Pushforward of sheaves of modules along a morphism of schemes preserves coproducts indexed
by a finite type. The functor is additive, hence preserves biproducts of shape `J` for every
finite `J : Type`; a finite index type in an arbitrary universe is brought into `Type` by an
equivalence with `Fin n`. -/
instance preservesColimitsOfShape_discrete_pushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    (I : Type u) [Finite I] :
    PreservesColimitsOfShape (Discrete I) (Scheme.Modules.pushforward i) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  exact preservesColimitsOfShape_of_equiv (Discrete.equivalence e).symm _

/-! ### Coproducts of an epimorphism of sheaves of modules -/

section MapFree

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison `free I ⟶ F.obj (free I)` of an epimorphism is an epimorphism.** If
`η : unit S ⟶ F.obj (unit R)` is an epimorphism and `F` preserves `I`-indexed coproducts, then
`SheafOfModules.mapFree F I η` is an epimorphism: the legs `F.map (ιFree j)` of the preserved
colimit cocone are jointly epic, and each composite `ιFree j ≫ mapFree F I η` is `η` followed by
such a leg. -/
theorem epi_mapFree (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) (I : Type u)
    (hF : PreservesColimitsOfShape (Discrete I) F)
    (η : SheafOfModules.unit S ⟶ F.obj (SheafOfModules.unit R)) (hη : Epi η) :
    Epi (SheafOfModules.mapFree F I η) := by
  refine ⟨fun g h hgh => ?_⟩
  refine (isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan I)).hom_ext ?_
  rintro ⟨j⟩
  have h1 : η ≫ F.map (SheafOfModules.ιFree j) ≫ g = η ≫ F.map (SheafOfModules.ιFree j) ≫ h := by
    rw [← Category.assoc, ← Category.assoc, ← SheafOfModules.ιFree_mapFree,
      Category.assoc, Category.assoc, hgh]
  exact (cancel_epi η).mp h1

end MapFree

/-! ### Global generating sections push forward -/

section GeneratingSections

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules)

/-- The comparison `free σ.I ⟶ i_* G` built from a family `σ` of global generating sections of
`G`: the coproduct comparison `free σ.I ⟶ i_* (free σ.I)` followed by the direct image of `σ`. -/
noncomputable def pushforwardGeneratorsHom (σ : G.GeneratingSections) :
    SheafOfModules.free (R := X.ringCatSheaf) σ.I ⟶ (Scheme.Modules.pushforward i).obj G :=
  SheafOfModules.mapFree (Scheme.Modules.pushforward i) σ.I (pushforwardUnitHom i) ≫
    (Scheme.Modules.pushforward i).map σ.π

/-- The coproduct comparison `free I ⟶ i_* (free I)` of a closed immersion is an epimorphism,
for a finite index type `I`. -/
theorem epi_mapFree_pushforwardUnitHom (I : Type u) [Finite I] :
    Epi (SheafOfModules.mapFree (Scheme.Modules.pushforward i) I (pushforwardUnitHom i)) :=
  epi_mapFree (Scheme.Modules.pushforward i) I
    (preservesColimitsOfShape_discrete_pushforward i I) (pushforwardUnitHom i)
    (epi_pushforwardUnitHom i)

/-- The comparison `free σ.I ⟶ i_* G` of finitely many global generating sections is an
epimorphism: it is the composite of two epimorphisms. -/
instance epi_pushforwardGeneratorsHom (σ : G.GeneratingSections) [σ.IsFiniteType] :
    Epi (pushforwardGeneratorsHom i G σ) := by
  have : Finite σ.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have h₁ := epi_mapFree_pushforwardUnitHom i σ.I
  have h₂ : Epi ((Scheme.Modules.pushforward i).map σ.π) :=
    @Functor.map_epi _ _ _ _ (Scheme.Modules.pushforward i) inferInstance _ _ σ.π
      (SheafOfModules.GeneratingSections.epi σ)
  exact @epi_comp _ _ _ _ _ _ h₁ _ h₂

/-- **Global generating sections push forward along a closed immersion.** A family of global
generating sections of `G` indexed by a finite type gives a family of global generating sections
of `i_* G` indexed by the same type. -/
noncomputable def generatingSectionsPushforward (σ : G.GeneratingSections) [σ.IsFiniteType] :
    ((Scheme.Modules.pushforward i).obj G).GeneratingSections :=
  Stacks.SheafOfModules.generatingSectionsOfEpi (pushforwardGeneratorsHom i G σ)

/-- The direct image of finitely many global generating sections is indexed by the same finite
type. -/
instance generatingSectionsPushforward_isFiniteType (σ : G.GeneratingSections)
    [σ.IsFiniteType] : (generatingSectionsPushforward i G σ).IsFiniteType :=
  ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := σ)⟩

end GeneratingSections

/-! ### Finite type and coherence of the direct image -/

section Coherence

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules)

/-- The restriction of `i_* G` to an affine open `V` of `X` has finitely many global generating
sections, when `G` is coherent: on the affine open `i ⁻¹ᵁ V` of `Z` the module `G` is the sheaf
associated with a finite module, so it has finitely many global generating sections there, and
those push forward along the closed immersion `i ∣_ V`. -/
theorem exists_finite_generatingSections_restrict_pushforward [G.IsCoherent]
    (V : X.affineOpens) :
    ∃ σ : (((Scheme.Modules.pushforward i).obj G).restrict (V : X.Opens).ι).GeneratingSections,
      Finite σ.I := by
  have hV : IsAffineOpen (i ⁻¹ᵁ (V : X.Opens)) := V.2.preimage i
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_isCoherent G _ hV
  obtain ⟨τ, hτ⟩ :=
    @Stacks.AlgebraicGeometry.CoherentTFAE.exists_finite_generatingSections_tilde _ M hM
  let τ' := SheafOfModules.GeneratingSections.equivOfIso e.symm
    (Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsPullbackTilde hV.isoSpec.hom M τ)
  have : τ'.IsFiniteType := ⟨hτ⟩
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso
    ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i
      (V : X.Opens)).app G).symm
    (generatingSectionsPushforward (i ∣_ (V : X.Opens)) _ τ'), hτ⟩

/-- **The direct image of a coherent module along a closed immersion is of finite type.** Being
of finite type is checked on the affine opens of `X`, which cover it, by
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_restrict_generatingSections`. -/
theorem isFiniteType_pushforward_of_isCoherent (h : G.IsCoherent) :
    ((Scheme.Modules.pushforward i).obj G).IsFiniteType := by
  choose σ hσ using exists_finite_generatingSections_restrict_pushforward i G
  exact Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_restrict_generatingSections _
    (fun V : X.affineOpens => (V : X.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top X)) σ hσ

/-- **Pushforward along a closed immersion preserves coherence.** For a closed immersion
`i : Z ⟶ X` into a locally Noetherian scheme and a coherent `𝒪_Z`-module `G`, the direct image
`i_* G` is a coherent `𝒪_X`-module: it is quasi-coherent by [Stacks, Tag 01LC] because a closed
immersion is quasi-compact and quasi-separated, it is of finite type by
`Stacks.ClosedImmersion.isFiniteType_pushforward_of_isCoherent`, and on a locally Noetherian
scheme a quasi-coherent module of finite type is coherent. -/
theorem isCoherent_pushforward [IsLocallyNoetherian X] (h : G.IsCoherent) :
    ((Scheme.Modules.pushforward i).obj G).IsCoherent := by
  have : G.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
  have := AlgebraicGeometry.pushforward_isQuasicoherent i G
  have := isFiniteType_pushforward_of_isCoherent i G h
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

end Coherence

end Stacks.ClosedImmersion

/-! ### The coherence equivalence of Stacks 0BK2 -/

namespace Stacks.LocalCohomology

/-- **Stacks Project, Tag 0BK2**, reverse implication of the coherence equivalence. Let
`j : U ⟶ X` be an open immersion, `x` a point of `U`, and `j'` the induced morphism from the
reduced closure of `{x}` in `U` to the reduced closure `Z` of `{j x}` in `X`. If the direct
image along `j'` of the structure sheaf of the reduced closure of `{x}` is coherent, then so is
its iterated direct image to `X`: the two iterated direct images around the square agree
(`AlgebraicGeometry.Scheme.Modules.pushforwardPointClosureIso`), and the other one is a direct
image along the closed immersion `Z ⟶ X`, which preserves coherence. -/
theorem isCoherent_pushforward_pointClosure_of_isCoherent_pushforward {U X : Scheme.{u}}
    (j : U ⟶ X) [IsLocallyNoetherian X] (x : U)
    (j' : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme)
    (comm : j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ≫ j)
    (h : ((Scheme.Modules.pushforward j').obj
      (SheafOfModules.unit
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj
      ((Scheme.Modules.pushforward
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subschemeι).obj
        (SheafOfModules.unit
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf))).IsCoherent :=
  have := Stacks.ClosedImmersion.isCoherent_pushforward
    (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subschemeι _ h
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (AlgebraicGeometry.Scheme.Modules.pushforwardPointClosureIso j x j' comm)

end Stacks.LocalCohomology

end
