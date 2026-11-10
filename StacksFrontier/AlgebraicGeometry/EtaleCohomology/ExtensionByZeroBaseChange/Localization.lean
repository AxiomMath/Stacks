module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# The small étale site of an étale object, as a localization

Let `B` be a big étale site, let `X` be a scheme in it, and let `j : U ⟶ X` be an object of
the small étale site of `X`. An étale scheme over `U` is in particular an étale scheme over
`X`, so composition with `j` is a functor from the small étale site of `U` to that of `X`.
This is the site functor whose direct image is the restriction functor `j^{-1}` of Stacks
03S3; its left adjoint on sheaves is extension by zero.

The functor is continuous. It is *not* representably flat — it does not preserve the final
object, and `StructuredArrow` over it fails to be cofiltered already for `U = X ⊔ X` — so
continuity is not available from the general flat criterion and is proved here from the two
halves of Stacks 00WW: the functor preserves the generating covering families, and it
preserves compatible families of sections. The second half uses that a morphism `W ⟶ U'`
over `X`, with `W` and `U'` étale over `X` and `U'` étale over `U`, exhibits `W` as an étale
scheme over `U` as well; that lift of `W` is what identifies the two restricted sections.

## Main definitions

* `AlgebraicGeometry.smallEtalePostcompose` — composition with `j : U ⟶ X` as a functor from
  the small étale site of `U` to the small étale site of `X`.

## Main results

* `AlgebraicGeometry.smallEtalePostcompose_isContinuous` — it is a continuous functor of
  sites.
* `AlgebraicGeometry.smallEtalePostcompose_coverPreserving` and
  `AlgebraicGeometry.smallEtalePostcompose_compatiblePreserving` — the two halves of that.
* `AlgebraicGeometry.faithful_smallEtalePostcompose` — it is always faithful, and
  `AlgebraicGeometry.full_smallEtalePostcompose` — it is full as soon as the structure
  morphism of `U` is a monomorphism.
* `CategoryTheory.Over.preservesLimitsOfShape_map_of_isConnected` — `Over.map` preserves
  connected limits.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 00WW](https://stacks.math.columbia.edu/tag/00WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w₀ v₀ u₀ u

namespace CategoryTheory.Over

end CategoryTheory.Over

namespace AlgebraicGeometry

namespace BigEtaleSite

variable (B : AlgebraicGeometry.BigEtaleSite.{u})

/-- A composite of morphisms of a big étale site which are étale as morphisms of schemes is
again étale. -/
public lemma etale_map_comp {W V T : B.Scheme} (g : W ⟶ V) (h : V ⟶ T)
    (hg : Etale (B.inclusion.map g)) (hh : Etale (B.inclusion.map h)) :
    Etale (B.inclusion.map (g ≫ h)) := by
  rw [Functor.map_comp]
  infer_instance

/-- If `g ≫ h` and `h` are étale as morphisms of schemes, then so is `g`. -/
public lemma etale_map_of_postcomp {W V T : B.Scheme} (g : W ⟶ V) (h : V ⟶ T) (k : W ⟶ T)
    (hk : Etale (B.inclusion.map k)) (hh : Etale (B.inclusion.map h)) (hw : g ≫ h = k) :
    Etale (B.inclusion.map g) := by
  apply MorphismProperty.of_postcomp @Etale (B.inclusion.map g) (B.inclusion.map h) hh
  rwa [← Functor.map_comp, hw]

end BigEtaleSite

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- Composition with the structure morphism of `U` sends an étale scheme over `U` to an
étale scheme over `X`. This is the site functor whose direct image is restriction of étale
sheaves from `X` to `U`. -/
public noncomputable def smallEtalePostcompose :
    SmallEtale B U.obj.left.1 U.obj.left.property ⥤ SmallEtale B X hX :=
  (BigEtaleOver.IsEtaleOver B X hX).lift
    (SmallEtale.inclusion B U.obj.left.1 U.obj.left.property ⋙ Over.map U.obj.hom)
    (fun V => B.etale_map_comp V.obj.hom U.obj.hom V.property U.property)

/-- Forgetting the étale condition identifies composition with `U ⟶ X` with the slice
functor `Over.map`, on both objects and morphisms. -/
public theorem smallEtalePostcompose_comp_inclusion :
    smallEtalePostcompose B X hX U ⋙ SmallEtale.inclusion B X hX =
      SmallEtale.inclusion B U.obj.left.1 U.obj.left.property ⋙ Over.map U.obj.hom :=
  rfl

/-- Composition with `U ⟶ X` is faithful: a morphism of the small étale site of `U` is
determined by its underlying morphism of schemes, and the functor does not change it. -/
public instance faithful_smallEtalePostcompose :
    (smallEtalePostcompose B X hX U).Faithful where
  map_injective {W W'} φ ψ h := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact congrArg
      (fun k : (smallEtalePostcompose B X hX U).obj W ⟶
        (smallEtalePostcompose B X hX U).obj W' => k.hom.left) h

/-- When the structure morphism of `U` is a monomorphism — for instance when `U ⟶ X` is an
open immersion — composition with it is full: a morphism over `X` between two étale schemes
over `U` is automatically a morphism over `U`, since its two composites into `X` agree and
`U ⟶ X` can be cancelled. -/
public instance full_smallEtalePostcompose [Mono U.obj.hom] :
    (smallEtalePostcompose B X hX U).Full where
  map_surjective {W W'} φ := by
    have hm : φ.hom.left ≫ W'.obj.hom ≫ U.obj.hom = W.obj.hom ≫ U.obj.hom := Over.w φ.hom
    refine ⟨ObjectProperty.homMk (Over.homMk φ.hom.left ?_), ?_⟩
    · exact (cancel_mono U.obj.hom).1 ((Category.assoc _ _ _).trans hm)
    · apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      rfl

/-- Composition with `U ⟶ X` preserves fibre products of small étale sites. -/
public instance preservesPullbacks_smallEtalePostcompose :
    PreservesLimitsOfShape WalkingCospan (smallEtalePostcompose B X hX U) := by
  have : PreservesLimitsOfShape WalkingCospan
      (smallEtalePostcompose B X hX U ⋙ SmallEtale.inclusion B X hX) := by
    rw [smallEtalePostcompose_comp_inclusion]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (SmallEtale.inclusion B X hX)

/-- Composition with `U ⟶ X` carries covering sieves of the small étale site of `U` to
covering sieves of the small étale site of `X`: a covering family is unchanged as a family
of schemes and arrows. -/
public lemma smallEtalePostcompose_coverPreserving :
    CoverPreserving (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X hX) (smallEtalePostcompose B X hX U) := by
  apply coverPreserving_of_generators
    (smallEtalePostcompose B X hX U)
    (SmallEtale.precoverage B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)
  intro Z R hR
  obtain ⟨E, rfl, hE⟩ :=
    (SmallEtale.mem_precoverage_iff B U.obj.left.1 U.obj.left.property).1 hR
  rw [← PreZeroHypercover.sieve₀_map]
  apply Precoverage.generate_mem_toGrothendieck
  apply (SmallEtale.mem_precoverage_iff B X hX).2
  exact ⟨E.map (smallEtalePostcompose B X hX U), rfl, hE⟩

/-- Composition with `U ⟶ X` preserves compatible families of sections. Given two morphisms
`f₁ : W ⟶ U₁` and `f₂ : W ⟶ U₂` of the small étale site of `X` whose composites into the
index object agree, the object `W` is itself étale over `U` through `f₁`, and the two
restrictions agree because they are restrictions along that single lift. -/
public lemma smallEtalePostcompose_compatiblePreserving :
    CompatiblePreserving.{u + 1} (SmallEtale.topology B X hX)
      (smallEtalePostcompose B X hX U) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ he
  let a₁ : W.obj.left ⟶ Y₁.obj.left := f₁.hom.left
  let a₂ : W.obj.left ⟶ Y₂.obj.left := f₂.hom.left
  have hw₁ : a₁ ≫ (Y₁.obj.hom ≫ U.obj.hom) = W.obj.hom := Over.w f₁.hom
  have hb₁ : g₁.hom.left ≫ Z.obj.hom = Y₁.obj.hom := Over.w g₁.hom
  have hb₂ : g₂.hom.left ≫ Z.obj.hom = Y₂.obj.hom := Over.w g₂.hom
  have hleft : a₁ ≫ g₁.hom.left = a₂ ≫ g₂.hom.left :=
    congrArg (fun k : W ⟶ (smallEtalePostcompose B X hX U).obj Z => k.hom.left) he
  have hW₁ : Etale (B.inclusion.map (a₁ ≫ Y₁.obj.hom)) :=
    B.etale_map_comp _ _
      (B.etale_map_of_postcomp a₁ (Y₁.obj.hom ≫ U.obj.hom) W.obj.hom W.property
        (B.etale_map_comp _ _ Y₁.property U.property) hw₁) Y₁.property
  let W' : SmallEtale B U.obj.left.1 U.obj.left.property :=
    ⟨Over.mk (a₁ ≫ Y₁.obj.hom), hW₁⟩
  let g₁' : W' ⟶ Y₁ := ObjectProperty.homMk (Over.homMk a₁ rfl)
  let g₂' : W' ⟶ Y₂ := ObjectProperty.homMk (Over.homMk a₂ (by
    change a₂ ≫ Y₂.obj.hom = a₁ ≫ Y₁.obj.hom
    rw [← hb₁, ← hb₂, ← Category.assoc, ← Category.assoc, hleft]))
  have hcompat : g₁' ≫ g₁ = g₂' ≫ g₂ :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext hleft)
  let e : (smallEtalePostcompose B X hX U).obj W' ≅ W :=
    (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι.preimageIso
      (Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ W.obj.hom = (a₁ ≫ Y₁.obj.hom) ≫ U.obj.hom
        rw [Category.id_comp, Category.assoc]
        exact hw₁.symm))
  have h : ∀ {Y} (g' : W' ⟶ Y) (f : W ⟶ (smallEtalePostcompose B X hX U).obj Y),
      g'.hom.left = f.hom.left → e.inv ≫ (smallEtalePostcompose B X hX U).map g' = f :=
    fun _ _ hf => ObjectProperty.hom_ext _ (Over.OverMorphism.ext ((Category.id_comp _).trans hf))
  have key := hx g₁' g₂' hg₁ hg₂ hcompat
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at key
  rw [← h g₁' f₁ rfl, ← h g₂' f₂ rfl, op_comp, op_comp, ℱ.obj.map_comp, ℱ.obj.map_comp]
  exact congrArg (ℱ.obj.map e.inv.op) key

/-- **Stacks 03S3.** Composition with an étale morphism `U ⟶ X` is a continuous functor from
the small étale site of `U` to the small étale site of `X`. Its direct image on sheaves is
restriction from `X` to `U`. -/
public instance smallEtalePostcompose_isContinuous :
    Functor.IsContinuous (smallEtalePostcompose B X hX U)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X hX) :=
  Functor.isContinuous_of_coverPreserving
    (smallEtalePostcompose_compatiblePreserving B X hX U)
    (smallEtalePostcompose_coverPreserving B X hX U)

end AlgebraicGeometry

end
