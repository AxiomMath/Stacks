module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp

/-!
# The affine subcategory is a dense subsite of the associated site (Stacks 0H0B)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `𝒳_{affine}` be its
affine subcategory (Stacks 0H0A). Stacks 0H0B says that the inclusion
`𝒳_{affine, τ} ⟶ 𝒳_τ` is a special cocontinuous functor, hence induces an equivalence of sheaf
topoi, for each of the five standard topologies `τ`.

The statement proved here is the general one: nothing about the particular topology is used
beyond the corresponding fact one level down, that the inclusion of the big affine category
over `S` into the big fppf category over `S` is a dense subsite for the topologies in question.
Given that, the affine inclusion of `𝒳` is special cocontinuous for the inherited topologies.
The five cases of the source are instances of this; the fppf one is stated separately.

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.inclusion_isSpecialCocontinuous`: **Stacks 0H0B**,
  in the form described above.
* `AlgebraicGeometry.Stack.AffineCategory.inclusion_isSpecialCocontinuous_fppf`:
  **Stacks 0H0B** for the fppf topology, whose dense-subsite input is Stacks 021V.
* `AlgebraicGeometry.Stack.AffineCategory.isFiberedInGroupoids_toAffine` and
  `.isCoverDense_inclusion`: the two ingredients, that the restricted structure functor is
  again fibred in groupoids and that the affine inclusion is cover dense.
* `CategoryTheory.Functor.inheritedTopology_id`,
  `CategoryTheory.Functor.mem_inheritedTopology_iff_functorPushforward` and
  `CategoryTheory.Functor.isDenseSubsite_inheritedTopology`: the general facts about inherited
  topologies that the proof rests on.

## Implementation notes

Cocontinuity of the affine inclusion for the inherited topologies is automatic once the
dense-subsite property holds, so the whole content is the dense-subsite property, and that in
turn reduces by `CategoryTheory.Functor.mem_inheritedTopology_iff_functorPushforward` to the
dense-subsite property one level down: a sieve of `𝒳_{affine}` is covering for the inherited
topology exactly when its pushforward to the big affine category is covering, and pushing
forward to the big fppf category over `S` commutes with the two routes because
`inclusion ⋙ p = toAffine ⋙ j` on the nose.

Cover density is the one place where fibredness in groupoids is used twice: the cover-by-image
sieve of `j` is covering downstairs, its cocontinuous lift is covering upstairs, and each of
its arrows is refined by an arrow out of an affine object, obtained by lifting the base
morphism and then filling in with the strongly cartesian property.

`CategoryTheory.Functor.inheritedTopology_id` is the equality of which
`AlgebraicGeometry.FibredSite.identity_inheritedTopology_le` is one inequality, for the
topologies `AlgebraicGeometry.BigFppfOver.baseOverTopology`.

## References

* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Functor

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

/-- The topology a category inherits from one of its own topologies along the identity functor
is that topology. -/
theorem inheritedTopology_id {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) :
    (𝟭 C).inheritedTopology J = J := by
  have hidPre : inheritedPrecoverage (𝟭 C) J.toPrecoverage = J.toPrecoverage := by
    ext X R
    exact ⟨fun hR => by simpa using hR.2,
      fun hR => ⟨fun {Y} g _ => isFiberedInGroupoids_id.isStronglyCartesian g, by simpa using hR⟩⟩
  show (inheritedPrecoverage (𝟭 C) J.toPrecoverage).toGrothendieck = J
  rw [hidPre]
  refine le_antisymm (GrothendieckTopology.toGrothendieck_toPrecoverage_le J) ?_
  intro X R hR
  have hR' : (R : Presieve X) ∈ J.toPrecoverage X := by
    show Sieve.generate (R : Presieve X) ∈ J X
    simpa using hR
  simpa using Precoverage.generate_mem_toGrothendieck (J := J.toPrecoverage) hR'

/-- For a category fibred in groupoids, the structure functor is continuous and cocontinuous for
the inherited topology and the original one. -/
private theorem isContinuous_and_isCocontinuous_inheritedTopology_of_isFiberedInGroupoids
    {C : Type u₁} [Category.{v₁} C] {Y : Type u₂} [Category.{v₂} Y] (p : Y ⥤ C) [HasPullbacks C]
    (J : GrothendieckTopology C) (hp : p.IsFiberedInGroupoids) :
    p.IsContinuous (p.inheritedTopology J) J ∧ p.IsCocontinuous (p.inheritedTopology J) J := by
  let : p.IsFibered := hp.isFibered
  let : (𝟭 C).IsFibered := isFiberedInGroupoids_id.isFibered
  have hpair := (isFibredOneMorphism_id p).isContinuous_and_isCocontinuous_inheritedTopology J
  rwa [inheritedTopology_id J] at hpair

/-- In a category fibred in groupoids, a morphism whose image factors through the image of
`g` factors through `g`. -/
private theorem exists_comp_eq_of_isFiberedInGroupoids {C : Type u₁} [Category.{v₁} C]
    {Y : Type u₂} [Category.{v₂} Y] {p : Y ⥤ C} (hp : p.IsFiberedInGroupoids) {a b c : Y}
    (g : b ⟶ c) (f : a ⟶ c) (χ : p.obj a ⟶ p.obj b) (h : p.map f = χ ≫ p.map g) :
    ∃ θ : a ⟶ b, θ ≫ g = f := by
  have := hp.isStronglyCartesian g
  obtain ⟨θ, ⟨_, hθ⟩, _⟩ := IsStronglyCartesian.universal_property p (p.map g) g χ (p.map f) h f
  exact ⟨θ, hθ⟩

/-- For a category fibred in groupoids, a sieve is covering for the inherited topology exactly
when its pushforward is covering for the original one. -/
theorem mem_inheritedTopology_iff_functorPushforward {C : Type u₁} [Category.{v₁} C]
    {Y : Type u₂} [Category.{v₂} Y] (p : Y ⥤ C) [HasPullbacks C]
    (J : GrothendieckTopology C) (hp : p.IsFiberedInGroupoids) {x : Y} (R : Sieve x) :
    R ∈ p.inheritedTopology J x ↔ R.functorPushforward p ∈ J (p.obj x) := by
  obtain ⟨hcont, hco⟩ :=
    isContinuous_and_isCocontinuous_inheritedTopology_of_isFiberedInGroupoids p J hp
  have : p.IsContinuous (p.inheritedTopology J) J := hcont
  refine ⟨fun hR => (CoverPreserving.of_isContinuous p (p.inheritedTopology J) J).cover_preserve
    hR, fun hR => ?_⟩
  have hpb : (R.functorPushforward p).functorPullback p ∈ p.inheritedTopology J x :=
    hco.cover_lift hR
  refine (p.inheritedTopology J).superset_covering ?_ hpb
  intro y f hf
  obtain ⟨z, g, χ, hg, hfac⟩ := hf
  obtain ⟨θ, hθ⟩ := exists_comp_eq_of_isFiberedInGroupoids hp g f χ hfac
  rw [← hθ]
  exact R.downward_closed hg θ

/-- A full and faithful, cover-dense inclusion of categories fibred in groupoids over a dense
subsite inclusion is itself a dense subsite inclusion for the inherited topologies, provided
the two routes to the base agree on pushforwards of sieves. -/
theorem isDenseSubsite_inheritedTopology {A : Type u₁} [Category.{v₁} A] {C : Type u₂}
    [Category.{v₂} C] {Y : Type u₃} [Category.{v₃} Y] {X : Type u₄} [Category.{v₄} X]
    [HasPullbacks A] [HasPullbacks C] (q : Y ⥤ A) (j : A ⥤ C) (i : Y ⥤ X) (p : X ⥤ C)
    (J : GrothendieckTopology A) (K : GrothendieckTopology C)
    (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids) (hbase : j.IsDenseSubsite J K)
    (hpush : ∀ (y : Y) (R : Sieve y),
      (R.functorPushforward i).functorPushforward p ∈ K (p.obj (i.obj y)) ↔
        (R.functorPushforward q).functorPushforward j ∈ K (j.obj (q.obj y)))
    [i.Full] [i.Faithful] (hcover : i.IsCoverDense (p.inheritedTopology K)) :
    i.IsDenseSubsite (q.inheritedTopology J) (p.inheritedTopology K) := by
  let : q.IsFiberedInGroupoids := hq
  let : p.IsFiberedInGroupoids := hp
  let : j.IsDenseSubsite J K := hbase
  refine ⟨hcover, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · intro y R
    have hs := mem_inheritedTopology_iff_functorPushforward (p := q) J hq (R := R)
    have ht := mem_inheritedTopology_iff_functorPushforward (p := p) K hp
      (R := R.functorPushforward i)
    exact ⟨fun hR => hs.mpr (hbase.functorPushforward_mem_iff.mp ((hpush y R).mp (ht.mp hR))),
      fun hR => ht.mpr ((hpush y R).mpr (hbase.functorPushforward_mem_iff.mpr (hs.mp hR)))⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack.AffineCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **Stacks 0H0B.** The structure functor of the affine subcategory of a category fibred in
groupoids is again fibred in groupoids, over the big affine fppf category of `S`. -/
@[stacks 0H0B "the affine structure functor is fibred in groupoids"]
theorem isFiberedInGroupoids_toAffine (hp : p.IsFiberedInGroupoids) :
    (toAffine B S hS p).IsFiberedInGroupoids := by
  let q := toAffine B S hS p
  let i := inclusion B S hS p
  let j := BigAffineFppf.inclusion B S hS
  refine ⟨fun {V U} f a ha => ?_, fun {a b c} φ ψ f hf => ?_⟩
  · have hcod : p.obj (i.obj a) = j.obj U :=
      (congrArg j.obj ha : j.obj (q.obj a) = j.obj U)
    obtain ⟨z, φ, hφ⟩ := hp.exists_lift (j.map f) (i.obj a) hcod
    have hz : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) := by
      rw [IsHomLift.domain_eq p (j.map f) φ]
      exact V.property
    let zA : AffineCategory B S hS p := ⟨z, hz⟩
    have hzA : q.obj zA = V :=
      ObjectProperty.FullSubcategory.ext (IsHomLift.domain_eq p (j.map f) φ)
    refine ⟨zA, ObjectProperty.homMk φ, IsHomLift.of_fac q f (ObjectProperty.homMk φ) hzA ha ?_⟩
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.eqToHom_hom, ObjectProperty.eqToHom_hom]
    exact IsHomLift.fac p (j.map f) φ
  · have hbase : j.map f ≫ p.map (i.map φ) = p.map (i.map ψ) := congrArg j.map hf
    obtain ⟨χ, ⟨hχ, hχfac⟩, huniq⟩ := hp.unique_lift (i.map φ) (i.map ψ) (j.map f) hbase
    refine ⟨i.preimage χ, ⟨?_, ?_⟩, fun χ'' hχ'' => ?_⟩
    · apply j.map_injective
      show p.map (i.map (i.preimage χ)) = j.map f
      rwa [i.map_preimage]
    · apply i.map_injective
      rwa [Functor.map_comp, i.map_preimage]
    · apply i.map_injective
      refine (huniq (i.map χ'') ⟨?_, ?_⟩).trans (i.map_preimage χ).symm
      · exact (congrArg j.map hχ''.1 : j.map (q.map χ'') = j.map f)
      · simpa using congrArg i.map hχ''.2

/-- **Stacks 0H0B.** The affine inclusion of a category fibred in groupoids is cover dense for
the inherited topology, as soon as the affine inclusion of the big fppf category over `S` is
cover dense. -/
@[stacks 0H0B "cover density"]
theorem isCoverDense_inclusion (hp : p.IsFiberedInGroupoids)
    (K : GrothendieckTopology (BigFppfOver B S hS))
    (hj : (BigAffineFppf.inclusion B S hS).IsCoverDense K) :
    (inclusion B S hS p).IsCoverDense (p.inheritedTopology K) := by
  classical
  refine ⟨fun a => ?_⟩
  have hco := (Functor.isContinuous_and_isCocontinuous_inheritedTopology_of_isFiberedInGroupoids
    p K hp).2
  refine (p.inheritedTopology K).superset_covering ?_
    (hco.cover_lift (hj.is_cover (p.obj a)))
  intro b f hf
  obtain ⟨⟨V, k, l, hfac⟩⟩ := hf
  obtain ⟨z, φ, hφ⟩ := hp.exists_lift l a rfl
  have hz : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) := by
    rw [IsHomLift.domain_eq p l φ]
    exact V.property
  have hl : eqToHom (IsHomLift.domain_eq p l φ).symm ≫ p.map φ = l := by
    simpa using (IsHomLift.fac p l φ).symm
  obtain ⟨θ, hθ⟩ := Functor.exists_comp_eq_of_isFiberedInGroupoids hp φ f
    (k ≫ eqToHom (IsHomLift.domain_eq p l φ).symm) (by rw [Category.assoc, hl, hfac])
  exact ⟨⟨⟨z, hz⟩, θ, φ, hθ⟩⟩

/-- **Stacks 0H0B.** The inclusion of the affine subcategory of a category fibred in groupoids
is a special cocontinuous functor from the associated affine site to the associated site, for
any topology on the big affine fppf category of `S` and any topology on the big fppf category
over `S` for which the affine inclusion downstairs is a dense subsite inclusion.

Consequently the inclusion induces an equivalence of sheaf topoi. The five topologies of the
source are the five instances. -/
@[stacks 0H0B]
theorem inclusion_isSpecialCocontinuous (hp : p.IsFiberedInGroupoids)
    (J : GrothendieckTopology (BigAffineFppf B S hS))
    (K : GrothendieckTopology (BigFppfOver B S hS))
    (hbase : (BigAffineFppf.inclusion B S hS).IsDenseSubsite J K) :
    IsSpecialCocontinuous (associatedAffineTopology B S hS p J) (p.inheritedTopology K)
      (inclusion B S hS p) := by
  classical
  let : p.IsFiberedInGroupoids := hp
  let : HasPullbacks (BigAffineFppf B S hS) := hasPullbacks_bigAffineFppf B S hS
  have hq : (toAffine B S hS p).IsFiberedInGroupoids := isFiberedInGroupoids_toAffine B S hS p hp
  have hpush : ∀ (a : AffineCategory B S hS p) (R : Sieve a),
      (R.functorPushforward (inclusion B S hS p)).functorPushforward p ∈
          K (p.obj ((inclusion B S hS p).obj a)) ↔
        (R.functorPushforward (toAffine B S hS p)).functorPushforward
            (BigAffineFppf.inclusion B S hS) ∈
          K ((BigAffineFppf.inclusion B S hS).obj ((toAffine B S hS p).obj a)) := by
    intro a R
    rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
    exact Iff.rfl
  have hdense : (inclusion B S hS p).IsDenseSubsite
      (associatedAffineTopology B S hS p J) (p.inheritedTopology K) :=
    Functor.isDenseSubsite_inheritedTopology (toAffine B S hS p)
      (BigAffineFppf.inclusion B S hS) (inclusion B S hS p) p J K hq hp hbase hpush
      (isCoverDense_inclusion B S hS p hp K hbase.isCoverDense)
  let : (inclusion B S hS p).IsDenseSubsite
    (associatedAffineTopology B S hS p J) (p.inheritedTopology K) := hdense
  exact ⟨inferInstance, hdense⟩

/-- **Stacks 0H0B** for the fppf topology: the inclusion of the affine subcategory into a
category fibred in groupoids is special cocontinuous from the associated affine fppf site to
the associated fppf site, and so induces an equivalence of the sheaf topoi. -/
@[stacks 0H0B "the fppf topology"]
theorem inclusion_isSpecialCocontinuous_fppf (hp : p.IsFiberedInGroupoids) :
    IsSpecialCocontinuous
      (associatedAffineTopology B S hS p (BigAffineFppf.topology B S hS))
      (associatedTopology B S hS p B.topology) (inclusion B S hS p) :=
  inclusion_isSpecialCocontinuous B S hS p hp (BigAffineFppf.topology B S hS)
    (BigFppfOver.topology B S hS) (bigAffineFppfInclusion_isDenseSubsite B S hS)

end AlgebraicGeometry.Stack.AffineCategory

end
