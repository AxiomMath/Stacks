module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Continuity
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationPushforward
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Descent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentation

/-!
# The site associated to a simplicial semi-representable object

Let `(C, J)` be a site and let `K` be a simplicial object of `SR(C)`. Each simplicial degree
carries the componentwise localization `C/K_n`, the disjoint union of the slices over the
components of the semi-representable object `K_n`, and a simplex map gives the componentwise
relocalization functor between two such. These functors are cocontinuous and have property P of
Stacks 09W7, so `n ↦ C/K_n` is a simplicial family of sites in case (B) of the simplicial-site
situation, with total site `(C/K)_total`.

The localization functor `j_0 : C/K_0 ⥤ C` is cocontinuous and its composite with a vertex
functor of any simplicial degree is the localization functor of that degree, so in particular
does not depend on the vertex: it is an augmentation towards `(C, J)` in the sense of case (B)
of Stacks 0D6Z. The morphisms of topoi `a_n : Sh(C/K_n) ⥤ Sh(C)` and
`a : Sh((C/K)_total) ⥤ Sh(C)` which Stacks 0D70 attaches to that augmentation are the morphisms
of topoi of the continuous and cocontinuous localization functors `j_n : C/K_n ⥤ C` and
`j_total : (C/K)_total ⥤ C`.

## Main definitions

* `CategoryTheory.SemiRepresentable.componentOverFunctor`: the functor
  `SR(C) ⥤ Cat` sending a semi-representable object `K` to the disjoint union `C/K` of the
  slices over its components and a morphism to the componentwise relocalization functor.
* `CategoryTheory.SimplicialSemiRepresentable.slices`: the simplicial object in categories
  `n ↦ C/K_n`.
* `CategoryTheory.SimplicialSemiRepresentable.sliceCoverings`: the covering families of
  `C/K_n`.
* `CategoryTheory.SimplicialSemiRepresentable.simplicialSite`: the simplicial family of sites
  `n ↦ C/K_n`, in case (B).
* `CategoryTheory.SimplicialSemiRepresentable.augmentation`: the augmentation towards `(C, J)`
  given by `j_0`.
* `CategoryTheory.SimplicialSemiRepresentable.localizationMorphism` and
  `.totalLocalizationMorphism`: the morphisms of topoi of `j_n` and of `j_total`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.totalPushforward_eq`: the total morphism of topoi
  of Stacks 0D70 and the morphism of topoi of `j_total` have equal direct images.
* `CategoryTheory.GrothendieckTopology.isSite_coverings`: the covering families of a
  Grothendieck topology satisfy the site axioms when all fibre products of covering families
  with arbitrary morphisms exist, which for these families means that the category has all fibre
  products, and
  `CategoryTheory.GrothendieckTopology.topologyOfCoverings_coverings`: they generate the
  topology they came from.
* `CategoryTheory.SemiRepresentable.componentwiseTopology_hasPullbacks`: those fibre products
  are inherited by the componentwise topology on `C/K`.
* `CategoryTheory.SimplicialSemiRepresentable.componentPushforwardIso` and
  `.componentInverseImageIso`: the degree-`n` morphism of topoi of Stacks 0D70 is the morphism
  of topoi of `j_n`.
* `CategoryTheory.SimplicialSemiRepresentable.totalPushforwardIso` and
  `.totalInverseImageIso`: the total morphism of topoi of Stacks 0D70 is the morphism of topoi
  of `j_total`.

## Implementation notes

The simplicial-site situation fixes one universe for the objects and the morphisms of its
component categories, so `C` is taken small and the index types of the semi-representable
objects `K_n` live in the same universe. No `AsSmall` presentation is then needed: the
augmentation site is `C` itself.

Making `n ↦ C/K_n` a *strict* simplicial object in `Cat` needs the componentwise
relocalization functors to be strictly functorial, which they are: both `CategoryTheory.Over.map`
and the inclusion of a component of a disjoint union are, and the index maps compose as plain
functions. That is `CategoryTheory.SemiRepresentable.componentOverFunctor`.

The site axioms for the covering families of `C/K_n` are an instance of a general fact: the
covering families of a Grothendieck topology satisfy them as soon as the fibre products called
for by the base change axiom exist. The standing hypothesis is therefore
`[J.toCoverage.HasPullbacks]`, the hypothesis under which Stacks 0D85 is formalized here. It is
stronger than the source's assumption that `C` is a site: the maximal presieve of an object is a
covering family of `J`, so the hypothesis asks for all fibre products in `C`. The constructions
for an arbitrary site, with the covering families along whose members all fibre products exist,
are in `StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableStacksSite`. The
fibre products are propagated to `C/K_n` componentwise: a cospan of a disjoint union of
categories lies in a single component, since the disjoint union has no arrows between
components, and the forgetful functor of a slice creates connected limits.

`CategoryTheory.SemiRepresentable.Continuity` carries private versions of the auxiliary facts
about arrows of a disjoint union used below (`ComponentOverHom` and friends); the versions here
are stated for a disjoint union of arbitrary categories instead, and used only for its
pullbacks.

The two identifications the source asserts are of different strengths here, and the difference
is in how Stacks 0D70 builds the two morphisms of topoi.

For the total site the cocontinuous functor out of the total category which Stacks 0D70 attaches
to the augmentation is `j_total` on the nose — this is the footnote in the proof of that
lemma — so the direct images are *equal*, and that is how it is recorded.

In simplicial degree `n` the morphism `a_n` of Stacks 0D70 is the composite of the degree-zero
morphism of topoi with the transition morphism of a vertex, so its direct image is a composite
of two direct images along cocontinuous functors, while the direct image of `j_n` is a single
one along their composite site functor. Those two agree only up to the canonical comparison, so
this identification is recorded as an isomorphism, and no equality holds between the
representatives at hand.

In both cases the identification of inverse images is obtained from uniqueness of left adjoints
against the identification of direct images, so the two halves cannot disagree. The inverse
images are genuinely only isomorphic even in the total case: the inverse image of the morphism
of topoi of a cocontinuous functor is the sheafification of the restriction, while that of a
continuous one is the restriction itself.

## References

* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ u

namespace CategoryTheory

/-! ### Disjoint unions of categories -/

namespace Sigma

variable {I : Type u} {D : I → Type u} [∀ i, SmallCategory (D i)]

section desc

variable {E : Type u} [SmallCategory E] {E' : Type u} [SmallCategory E']

/-- The inclusion of a component followed by a functor assembled from its restrictions to the
components is the restriction to that component, as an equality of functors. -/
theorem incl_comp_desc (F : ∀ i, D i ⥤ E) (i : I) :
    CategoryTheory.Sigma.incl (C := D) i ⋙ CategoryTheory.Sigma.desc F = F i := rfl

/-- Postcomposing a functor assembled from its restrictions to the components is assembling the
postcomposites. -/
theorem desc_comp (F : ∀ i, D i ⥤ E) (H : E ⥤ E') :
    CategoryTheory.Sigma.desc F ⋙ H = CategoryTheory.Sigma.desc fun i => F i ⋙ H := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  rintro ⟨i, X⟩ ⟨j, Y⟩ ⟨f⟩
  rfl

/-- The functor assembled from the component inclusions is the identity. -/
theorem desc_incl :
    CategoryTheory.Sigma.desc (fun i => CategoryTheory.Sigma.incl (C := D) i) = 𝟭 (Σ i, D i) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  rintro ⟨i, X⟩ ⟨j, Y⟩ ⟨f⟩
  rfl

end desc

section pullback

variable {i : I} {X Y P Z : D i} {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The image of a pullback square under the inclusion of a component of a disjoint union of
categories is a pullback square. -/
theorem isPullback_incl_map (h : IsPullback p₁ p₂ f g) :
    IsPullback ((CategoryTheory.Sigma.incl (C := D) i).map p₁)
      ((CategoryTheory.Sigma.incl (C := D) i).map p₂)
      ((CategoryTheory.Sigma.incl (C := D) i).map f)
      ((CategoryTheory.Sigma.incl (C := D) i).map g) := by
  -- an arrow into the component `i` automatically comes from the component `i`
  have key : ∀ (W : Σ j, D j) (a : W ⟶ (⟨i, X⟩ : Σ j, D j)) (b : W ⟶ (⟨i, Y⟩ : Σ j, D j)),
      a ≫ (CategoryTheory.Sigma.incl (C := D) i).map f =
        b ≫ (CategoryTheory.Sigma.incl (C := D) i).map g →
      ∃! l : W ⟶ (⟨i, P⟩ : Σ j, D j),
        l ≫ (CategoryTheory.Sigma.incl (C := D) i).map p₁ = a ∧
          l ≫ (CategoryTheory.Sigma.incl (C := D) i).map p₂ = b := by
    rintro ⟨j, W⟩ ⟨a⟩ ⟨b⟩ hab
    refine ⟨.mk (h.lift a b (Sigma.SigmaHom.mk.inj hab)),
      ⟨congrArg Sigma.SigmaHom.mk (h.lift_fst _ _ _),
        congrArg Sigma.SigmaHom.mk (h.lift_snd _ _ _)⟩, ?_⟩
    rintro ⟨m⟩ ⟨h₁, h₂⟩
    exact congrArg Sigma.SigmaHom.mk
      (h.hom_ext ((Sigma.SigmaHom.mk.inj h₁).trans (h.lift_fst _ _ _).symm)
        ((Sigma.SigmaHom.mk.inj h₂).trans (h.lift_snd _ _ _).symm))
  choose l hl using key
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_
    (fun s => l s.pt s.fst s.snd s.condition) (fun s => (hl _ _ _ s.condition).1.1)
    (fun s => (hl _ _ _ s.condition).1.2) fun s m h₁ h₂ => (hl _ _ _ s.condition).2 m ⟨h₁, h₂⟩)
  exact congrArg Sigma.SigmaHom.mk h.w

end pullback

end Sigma

/-! ### The covering families of a Grothendieck topology -/

section IsSite

variable {C : Type u} [SmallCategory C]

/-- Postcomposing a covering family with an isomorphism of its target coming from an equality of
objects leaves it covering. -/
private theorem mem_coverings_comp_eqToHom {P : Precoverage C} {A B : C} (e : A = B)
    {ι : Type u} (X : ι → C) (f : ∀ j, X j ⟶ A) (hf : Presieve.ofArrows X f ∈ P A) :
    Presieve.ofArrows X (fun j => f j ≫ eqToHom e) ∈ P B := by
  subst e
  simpa using hf

/-- The covering families of a Grothendieck topology — those whose generated sieve is
covering — satisfy the isomorphism, composition and base change axioms of a site, provided the
fibre products required by the base change axiom exist. This is what makes a Grothendieck
topology presentable by covering families, as the simplicial-site situation requires.

The hypothesis is much stronger than the base change axiom of a site. The maximal presieve of an
object generates the maximal sieve, so it is a covering family of `J`, and
`[J.toCoverage.HasPullbacks]` asks for the fibre product of every pair of morphisms with a common
target: it holds exactly when the category has all fibre products. For an arbitrary site, the
covering families of `J` along whose members all fibre products exist are the ones satisfying the
site axioms; that is `CategoryTheory.GrothendieckTopology.isSite_stableCoverings`. -/
@[sga "3 IV 4.6.4" "special case"]
theorem GrothendieckTopology.isSite_coverings (J : GrothendieckTopology C)
    [J.toCoverage.HasPullbacks] :
    IsSite (fun 𝒰 : Covering.{u, u, u} C => 𝒰.2.presieve₀ ∈ J.toCoverage 𝒰.1) := by
  have key : ∀ (U : C) (R : Presieve U), R ∈ J.toCoverage U ↔ R ∈ J.toPrecoverage U :=
    fun _ _ => Iff.rfl
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    rw [key, PreZeroHypercover.presieve₀_singleton]
    exact Precoverage.HasIsos.mem_coverings_of_isIso (J := J.toPrecoverage) f
  · intro 𝒰 h𝒰 𝒱 h𝒱 h
    rw [key] at h𝒰 ⊢
    refine Precoverage.IsStableUnderComposition.comp_mem_coverings
      (J := J.toPrecoverage) 𝒰.2.f h𝒰 (fun i j => (𝒱 i).2.f j ≫ eqToHom (h i)) fun i => ?_
    exact mem_coverings_comp_eqToHom (h i) _ _ (by rw [← key]; exact h𝒱 i)
  · intro 𝒰 h𝒰 V g
    have hpb : 𝒰.2.presieve₀.HasPullbacks g := Precoverage.hasPullbacks_of_mem g h𝒰
    have : ∀ i, HasPullback (𝒰.2.f i) g := fun i => hpb.hasPullback (𝒰.2.presieve₀_f i)
    refine ⟨fun i => Limits.pullback (𝒰.2.f i) g, fun i => Limits.pullback.fst _ _,
      fun i => Limits.pullback.snd _ _, fun i => IsPullback.of_hasPullback _ _, ?_⟩
    change _ ∈ J.toCoverage V
    rw [key]
    exact Precoverage.IsStableUnderBaseChange.mem_coverings_of_isPullback
      (J := J.toPrecoverage) 𝒰.2.f (by rw [← key]; exact h𝒰) g _ _
      fun i => (IsPullback.of_hasPullback (𝒰.2.f i) g).flip

/-- The topology generated by the covering families of a Grothendieck topology is that
topology. -/
theorem GrothendieckTopology.topologyOfCoverings_coverings (J : GrothendieckTopology C) :
    topologyOfCoverings (fun 𝒰 : Covering.{u, u, u} C => 𝒰.2.presieve₀ ∈ J.toCoverage 𝒰.1) = J := by
  apply le_antisymm
  · change Precoverage.toGrothendieck _ ≤ J
    refine Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr fun U R hR => ?_
    obtain ⟨E, hE, rfl⟩ := hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    exact hE
  · intro U S hS
    let E : PreZeroHypercover.{u} U :=
      ⟨Σ V : C, {f : V ⟶ U // S f}, fun p => p.1, fun p => p.2.1⟩
    have hgen : Sieve.generate E.presieve₀ = S := by
      refine le_antisymm ?_ ?_
      · rintro V f ⟨W, h, g, ⟨p⟩, rfl⟩
        exact S.downward_closed p.2.2 h
      · intro V f hf
        exact ⟨V, 𝟙 V, f, .mk (⟨V, ⟨f, hf⟩⟩ : Σ V : C, {f : V ⟶ U // S f}), by simp⟩
    have hcov : E.presieve₀ ∈ J.toCoverage U := by
      rw [GrothendieckTopology.mem_toCoverage_iff, hgen]
      exact hS
    rw [← hgen]
    exact Precoverage.generate_mem_toGrothendieck ⟨E, hcov, rfl⟩

end IsSite

/-! ### Fibre products in a slice category -/

/-- A cospan of a slice category has a pullback as soon as the cospan of the underlying arrows
has one in the base: the forgetful functor of a slice creates connected limits, and a cospan is
a connected diagram. -/
theorem Over.hasPullback_of_left {C : Type u} [SmallCategory C] {Z : C} {A B T : Over Z}
    (f : A ⟶ T) (g : B ⟶ T) [HasPullback f.left g.left] : HasPullback f g := by
  let : HasLimit (cospan ((cospan f g ⋙ Over.forget Z).map WalkingCospan.Hom.inl)
      ((cospan f g ⋙ Over.forget Z).map WalkingCospan.Hom.inr)) :=
    inferInstanceAs (HasPullback f.left g.left)
  let : HasLimit (cospan f g ⋙ Over.forget Z) := hasLimit_of_iso (diagramIsoCospan _).symm
  exact hasLimit_of_created (cospan f g) (Over.forget Z)

/-! ### The site of a semi-representable object, functorially -/

namespace SemiRepresentable

variable {C : Type u} [SmallCategory C]

/-- The fibre products required by the base change axiom for the componentwise topology on
`C/K` exist as soon as those required by the base change axiom for `J` do. A cospan of `C/K`
lies in a single component, where it is a cospan of a slice of `C`; the arrow being based
changed lies in a covering sieve of `J` after forgetting the structure morphism. -/
instance componentwiseTopology_hasPullbacks (J : GrothendieckTopology C)
    [J.toCoverage.HasPullbacks] (K : FormalCoproduct.{u} C) :
    (componentwiseTopology J K).toCoverage.HasPullbacks where
  hasPullbacks_of_mem := by
    rintro W ⟨i, Y⟩ R ⟨f⟩ hR
    refine { hasPullback := ?_ }
    rintro Z ⟨h⟩ hh
    have hS : (Sieve.generate R).functorPullback
        (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i) ∈
          J.over (K.obj i) Y := hR
    have hhS : ((Sieve.generate R).functorPullback
        (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i)).arrows h :=
      Sieve.le_generate R _ _ hh
    have hT := (J.over_forget_coverPreserving (K.obj i)).cover_preserve hS
    have hTcov : (Sieve.functorPushforward (Over.forget (K.obj i))
        ((Sieve.generate R).functorPullback
          (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i))).arrows ∈
        J.toCoverage Y.left := by
      rw [GrothendieckTopology.mem_toCoverage_iff, Sieve.generate_sieve]
      exact hT
    have : HasPullback h.left f.left :=
      (Precoverage.hasPullbacks_of_mem f.left hTcov).hasPullback
        ⟨_, h, 𝟙 _, hhS, (Category.id_comp _).symm⟩
    have : HasPullback h f := Over.hasPullback_of_left h f
    exact (CategoryTheory.Sigma.isPullback_incl_map
      (D := fun j : K.I => Over (K.obj j)) (i := i)
      (IsPullback.of_hasPullback h f)).hasPullback

/-- The componentwise relocalization functor `C/K ⥤ C/L` of a morphism `f : K ⟶ L` of
semi-representable objects: on the component indexed by `i` it is relocalization along
`f.φ i` followed by the inclusion of the component indexed by `f.f i`. -/
def componentOverMap {K L : FormalCoproduct.{u} C} (f : K ⟶ L) :
    ComponentOver K ⥤ ComponentOver L :=
  CategoryTheory.Sigma.desc fun i =>
    Over.map (f.φ i) ⋙ CategoryTheory.Sigma.incl (C := fun j : L.I => Over (L.obj j)) (f.f i)

/-- The componentwise localization functor `C/K ⥤ C`. -/
def componentOverForget (K : FormalCoproduct.{u} C) : ComponentOver K ⥤ C :=
  CategoryTheory.Sigma.desc fun i => Over.forget (K.obj i)

/-- Bridge: the relocalization functor of a localization datum is the componentwise
relocalization functor of its morphism. -/
theorem LocalizationSites.relocalizationFunctor_eq {J : GrothendieckTopology C}
    (S : LocalizationSites.{u} C J) : S.relocalizationFunctor = componentOverMap S.f := rfl

/-- Bridge: the localization functor of a localization datum is the componentwise localization
functor of its source. -/
theorem LocalizationSites.localizationFunctor_eq {J : GrothendieckTopology C}
    (S : LocalizationSites.{u} C J) : S.localizationFunctor = componentOverForget S.K := rfl

/-- Relocalizing and then localizing is localizing: the componentwise relocalization functor of
`f : K ⟶ L` followed by the localization functor of `L` is the localization functor of `K`. -/
theorem componentOverMap_comp_componentOverForget {K L : FormalCoproduct.{u} C} (f : K ⟶ L) :
    componentOverMap f ⋙ componentOverForget L = componentOverForget K := by
  simp only [componentOverMap, componentOverForget]
  rw [CategoryTheory.Sigma.desc_comp]
  refine congrArg CategoryTheory.Sigma.desc (funext fun i => ?_)
  rw [Functor.assoc, CategoryTheory.Sigma.incl_comp_desc]
  rfl

theorem componentOverMap_id (K : FormalCoproduct.{u} C) :
    componentOverMap (𝟙 K) = 𝟭 (ComponentOver K) := by
  have h : (fun i : K.I => Over.map (FormalCoproduct.Hom.φ (𝟙 K) i) ⋙
      CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j))
        (FormalCoproduct.Hom.f (𝟙 K) i)) =
      fun i : K.I => CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i := by
    funext i
    rw [show FormalCoproduct.Hom.φ (𝟙 K) i = 𝟙 (K.obj i) from rfl, Over.mapId_eq]
    exact Functor.id_comp _
  rw [componentOverMap, h, CategoryTheory.Sigma.desc_incl]

theorem componentOverMap_comp {K L M : FormalCoproduct.{u} C} (f : K ⟶ L) (g : L ⟶ M) :
    componentOverMap (f ≫ g) = componentOverMap f ⋙ componentOverMap g := by
  simp only [componentOverMap]
  rw [CategoryTheory.Sigma.desc_comp]
  refine congrArg CategoryTheory.Sigma.desc (funext fun i => ?_)
  rw [Functor.assoc, CategoryTheory.Sigma.incl_comp_desc,
    show FormalCoproduct.Hom.φ (f ≫ g) i = f.φ i ≫ g.φ (f.f i) from rfl,
    Over.mapComp_eq, Functor.assoc]
  rfl

/-- The site `C/K` of a semi-representable object, as a functor on `SR(C) = FormalCoproduct C`:
a morphism of semi-representable objects goes to the componentwise relocalization functor of
Stacks 0D85. Relocalization is strictly functorial, so this is a functor and not merely a
pseudofunctor; that is what makes `n ↦ C/K_n` a simplicial object in `Cat`. It carries no
attribute: the source states the continuity properties of the relocalization functors, not this
functoriality. -/
def componentOverFunctor : FormalCoproduct.{u} C ⥤ Cat.{u, u} where
  obj K := Cat.of (ComponentOver K)
  map f := (componentOverMap f).toCatHom
  map_id K := congr($(componentOverMap_id K).toCatHom)
  map_comp f g := congr($(componentOverMap_comp f g).toCatHom)

end SemiRepresentable

/-! ### Functors out of a Grothendieck construction built from equal fibrewise data -/

namespace Grothendieck

variable {A : Type u₁} [Category.{v₁} A] {F : A ⥤ Cat.{u, u}} {E : Type u} [SmallCategory E]

/-- Two functors out of a Grothendieck construction built from fibrewise data whose transitions
are transports along equalities agree as soon as their fibrewise functors do: the transitions and
the coherences are then proofs of the same propositions. -/
theorem functorFromOfEq_congr (fib fib' : ∀ c, F.obj c ⥤ E)
    (e : ∀ {c c' : A} (f : c ⟶ c'), fib c = (F.map f).toFunctor ⋙ fib c')
    (e' : ∀ {c c' : A} (f : c ⟶ c'), fib' c = (F.map f).toFunctor ⋙ fib' c')
    (hom_id) (hom_comp) (hom_id') (hom_comp') (h : fib = fib') :
    Grothendieck.functorFromOfEq fib (fun f => eqToHom (e f)) hom_id hom_comp =
      Grothendieck.functorFromOfEq fib' (fun f => eqToHom (e' f)) hom_id' hom_comp' := by
  subst h
  rfl

end Grothendieck

/-! ### Whiskering a transport along an equality of functors -/

theorem Functor.whiskerLeft_eqToHom {A B D : Type*} [Category A] [Category B] [Category D]
    (G : A ⥤ B) {H H' : B ⥤ D} (h : H = H') :
    Functor.whiskerLeft G (eqToHom h) = eqToHom (congrArg (fun F => G ⋙ F) h) := by
  subst h
  rfl

/-! ### The simplicial site of a simplicial semi-representable object -/

namespace SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C))

/-- The simplicial object in categories underlying `C/K`: its degree `n` part is the
componentwise localization `C/K_n` and the functor attached to a simplex map `φ : [m] ⟶ [n]` is
the componentwise relocalization functor along `K_n ⟶ K_m`. -/
def slices : SimplicialObject Cat.{u, u} := K ⋙ componentOverFunctor

theorem slices_obj (n : SimplexCategoryᵒᵖ) :
    (slices K).obj n = Cat.of (ComponentOver (K.obj n)) := rfl

theorem slices_map {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) :
    ((slices K).map φ).toFunctor = componentOverMap (K.map φ) := rfl

/-- The localization functor `j_n : C/K_n ⥤ C` of the site in simplicial degree `n`. -/
def sliceForget (n : SimplexCategoryᵒᵖ) : ((slices K).obj n : Cat.{u, u}) ⥤ C :=
  componentOverForget (K.obj n)

theorem sliceForget_eq (n : SimplexCategoryᵒᵖ) :
    sliceForget K n = componentOverForget (K.obj n) := rfl

/-- Relocalizing along a simplex map and then localizing is localizing: the transition functor
of a simplex map followed by `j_n` is `j_m`. -/
theorem slicesMap_comp_sliceForget {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) :
    ((slices K).map φ).toFunctor ⋙ sliceForget K n = sliceForget K m :=
  componentOverMap_comp_componentOverForget (K.map φ)

/-- The covering families of the componentwise localization `C/K_n`: those whose generated sieve
is covering for the componentwise localized topology. -/
def sliceCoverings (n : SimplexCategoryᵒᵖ) :
    Covering.{u, u, u} (ComponentOver (K.obj n)) → Prop := fun 𝒰 =>
  𝒰.2.presieve₀ ∈ (componentwiseTopology J (K.obj n)).toCoverage 𝒰.1

/-- The covering families of `C/K_n` generate the componentwise localized topology. -/
theorem topologyOfCoverings_sliceCoverings (n : SimplexCategoryᵒᵖ) :
    topologyOfCoverings (sliceCoverings J K n) = componentwiseTopology J (K.obj n) :=
  GrothendieckTopology.topologyOfCoverings_coverings _

/-- The localization datum of a simplex map: the semi-representable objects in the two degrees
together with the morphism between them. -/
def transitionSites {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) : LocalizationSites.{u} C J :=
  ⟨K.obj m, K.obj n, K.map φ⟩

/-- The transition functor of a simplex map is cocontinuous for the topologies generated by the
covering families of the two degrees. This is Stacks 0D85 for the morphism `K_n ⟶ K_m` of
semi-representable objects. -/
theorem isCocontinuous_sliceCoverings {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) :
    (componentOverMap (K.map φ)).IsCocontinuous (topologyOfCoverings (sliceCoverings J K m))
      (topologyOfCoverings (sliceCoverings J K n)) := by
  rw [topologyOfCoverings_sliceCoverings, topologyOfCoverings_sliceCoverings]
  exact LocalizationSites.relocalizationFunctor_isCocontinuous (transitionSites J K φ)

/-! ### The localization functor of the total site -/

theorem totalForget_fib_eq {c c' : SimplexCategoryᵒᵖ} (f : c ⟶ c') :
    sliceForget K c = ((slices K).map f).toFunctor ⋙ sliceForget K c' :=
  (slicesMap_comp_sliceForget K f).symm

theorem totalForget_fib_eq_id (c : SimplexCategoryᵒᵖ) :
    eqToHom (totalForget_fib_eq K (𝟙 c)) =
      eqToHom (Grothendieck.fib_map_id_eq (F := slices K) (sliceForget K) c) := rfl

theorem totalForget_fib_eq_comp (c₁ c₂ c₃ : SimplexCategoryᵒᵖ) (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) :
    eqToHom (totalForget_fib_eq K (f ≫ g)) =
      eqToHom (totalForget_fib_eq K f) ≫
        Functor.whiskerLeft ((slices K).map f).toFunctor (eqToHom (totalForget_fib_eq K g)) ≫
          eqToHom (Grothendieck.fib_map_comp_eq (F := slices K) (sliceForget K) f g) := by
  rw [Functor.whiskerLeft_eqToHom, eqToHom_trans, eqToHom_trans]

/-- The localization functor `j_total : (C/K)_total ⥤ C` of the total site: in simplicial degree
`c` it is the localization functor `j_c : C/K_c ⥤ C`. -/
def totalForget : Grothendieck (slices K) ⥤ C :=
  Grothendieck.functorFromOfEq (F := slices K) (sliceForget K)
    (fun {_ _} f => eqToHom (totalForget_fib_eq K f))
    (totalForget_fib_eq_id K) (totalForget_fib_eq_comp K)

/-- The inclusion of the component in simplicial degree `c` followed by `j_total` is `j_c`. -/
theorem ι_comp_totalForget (c : SimplexCategoryᵒᵖ) :
    Grothendieck.ι (slices K) c ⋙ totalForget K = sliceForget K c := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun y z f => ?_
  simp only [Functor.comp_map, totalForget, Grothendieck.functorFromOfEq, Grothendieck.ι,
    eqToHom_app, CategoryTheory.Functor.map_comp]
  rw [eqToHom_comp_map_eqToHom_assoc]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The localization functor `j_c : C/K_c ⥤ C` is continuous for the componentwise localized
topology, by Stacks 0D85. -/
theorem sliceForget_isContinuous_componentwise (c : SimplexCategoryᵒᵖ) :
    (sliceForget K c).IsContinuous (componentwiseTopology J (K.obj c)) J :=
  LocalizationSites.localizationFunctor_isContinuous
    (⟨K.obj c, K.obj c, 𝟙 _⟩ : LocalizationSites.{u} C J)

/-! ### The simplicial family of sites -/

variable [J.toCoverage.HasPullbacks]

/-- The covering families of `C/K_n` satisfy the site axioms. -/
theorem isSite_sliceCoverings (n : SimplexCategoryᵒᵖ) : IsSite (sliceCoverings J K n) :=
  GrothendieckTopology.isSite_coverings (componentwiseTopology J (K.obj n))

/-- The transition functor of a simplex map has property P of Stacks 09W7 for the covering
families of the two degrees. This is Stacks 0D85 for the morphism `K_n ⟶ K_m` of
semi-representable objects. -/
theorem hasCoverPullbacks_sliceCoverings {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) :
    Functor.HasCoverPullbacks (componentOverMap (K.map φ)) (sliceCoverings J K m)
      (sliceCoverings J K n) :=
  LocalizationSites.relocalizationFunctor_hasCoverPullbacks (transitionSites J K φ)

/-- The simplicial family of sites `n ↦ C/K_n` attached to a simplicial object `K` of `SR(C)`,
in case (B): the transition functors are cocontinuous and have property P of Stacks 09W7, both
by Stacks 0D85.

This is the construction which precedes Stacks 0D8B rather than part of its statement, which
presupposes this simplicial site and asserts only the identifications of morphisms of topoi
below; it therefore carries no attribute. -/
def simplicialSite : CocontinuousSimplicialSite.{u} where
  underlying := slices K
  coverage := sliceCoverings J K
  isSite n := isSite_sliceCoverings J K n
  isCocontinuous {_ _} φ := isCocontinuous_sliceCoverings J K φ
  hasCoverPullbacks {_ _} φ := hasCoverPullbacks_sliceCoverings J K φ

/-- The simplicial family of sites `n ↦ C/K_n`, read as a simplicial-site situation. -/
def situation : SimplicialSiteSituation.{u} := ⟨Sum.inr (simplicialSite J K)⟩

theorem component_eq (n : SimplexCategory) :
    (situation J K).component n = Cat.of (ComponentOver (K.obj (op n))) := rfl

/-- The topology of the component site in degree `n` is the componentwise localized topology of
`C/K_n`. -/
theorem componentTopology_eq (n : SimplexCategory) :
    (situation J K).componentTopology n = componentwiseTopology J (K.obj (op n)) :=
  topologyOfCoverings_sliceCoverings J K (op n)

theorem totalTopology_eq :
    (situation J K).totalTopology =
      SimplicialCoverings.totalTopology (slices K) (sliceCoverings J K) := rfl

/-! ### Continuity and cocontinuity of the localization functors -/

/-- The localization functor `j_n : C/K_n ⥤ C` is continuous, by Stacks 0D85. -/
instance sliceForget_isContinuous (n : SimplexCategory) :
    (sliceForget K (op n)).IsContinuous ((situation J K).componentTopology n) J := by
  rw [componentTopology_eq]
  exact LocalizationSites.localizationFunctor_isContinuous
    (⟨K.obj (op n), K.obj (op n), 𝟙 _⟩ : LocalizationSites.{u} C J)

/-- The localization functor `j_n : C/K_n ⥤ C` is cocontinuous, by Stacks 0D85. -/
instance sliceForget_isCocontinuous (n : SimplexCategory) :
    (sliceForget K (op n)).IsCocontinuous ((situation J K).componentTopology n) J := by
  rw [componentTopology_eq]
  exact LocalizationSites.localizationFunctor_isCocontinuous
    (⟨K.obj (op n), K.obj (op n), 𝟙 _⟩ : LocalizationSites.{u} C J)

/-- The transition functor of a simplex map is cocontinuous for the component topologies of the
simplicial site. -/
instance componentOverMap_isCocontinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentOverMap (K.map φ.op)).IsCocontinuous ((situation J K).componentTopology n)
      ((situation J K).componentTopology m) :=
  (simplicialSite J K).isCocontinuous φ.op

/-! ### The augmentation defined by the degree-zero localization functor -/

/-- The special case under `[J.toCoverage.HasPullbacks]` of Stacks 0D8B, whose tag is on
`CategoryTheory.SimplicialSemiRepresentable.stableAugmentation` for an arbitrary site. The
localization functor `j_0 : C/K_0 ⥤ C` defines an augmentation of the simplicial site `n ↦ C/K_n`
towards `(C, J)`, as in case (B) of Stacks 0D6Z: it is cocontinuous, and its composite with the
functor of a vertex of simplicial degree `n` is the localization functor `j_n`, which does not
mention the vertex. -/
def augmentation : (simplicialSite J K).Augmentation (Cat.of C) J where
  functor := sliceForget K (op (SimplexCategory.mk 0))
  isCocontinuous := sliceForget_isCocontinuous J K (SimplexCategory.mk 0)
  compatibility _ φ ψ :=
    (slicesMap_comp_sliceForget K φ.op).trans (slicesMap_comp_sliceForget K ψ.op).symm

/-- The augmentation of the simplicial-site situation attached to `K`. -/
def situationAugmentation :
    SimplicialSiteSituation.Augmentation (situation J K) (Cat.of C) J :=
  augmentation J K

/-- The special case under `[J.toCoverage.HasPullbacks]` of Stacks 0D8B, whose tag is on
`CategoryTheory.SimplicialSemiRepresentable.stableAugmentation_functor` for an arbitrary site. The
functor underlying that augmentation is the degree-zero localization functor `j_0`. Together with
`CategoryTheory.SimplicialSemiRepresentable.augmentation` this is the assertion that `j_0` defines
the augmentation. -/
theorem augmentation_functor :
    (augmentation J K).functor = sliceForget K (op (SimplexCategory.mk 0)) := rfl

/-- The functor attached to simplicial degree `c` by the augmentation — the vertex functor of
that degree followed by `j_0` — is the localization functor `j_c` of that degree. -/
theorem totalAugmentationFibre_eq_sliceForget (c : SimplexCategoryᵒᵖ) :
    CocontinuousSimplicialSite.Augmentation.totalAugmentationFibre (augmentation J K) c =
      sliceForget K c :=
  slicesMap_comp_sliceForget K (CocontinuousSimplicialSite.degreeZeroVertexOp c)

/-- The functor out of the total category attached to the augmentation `j_0` is the localization
functor `j_total` of the total site.

This is the footnote in the proof of Stacks 0D70 relating `a` to `j_total`, and so an ingredient
of the proof of Stacks 0D8B rather than a part of its statement; it carries no attribute. -/
theorem totalAugmentationFunctor_eq :
    CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor (augmentation J K) =
      totalForget K := by
  have h : CocontinuousSimplicialSite.Augmentation.totalAugmentationFibre (augmentation J K) =
      sliceForget K :=
    funext fun c => totalAugmentationFibre_eq_sliceForget J K c
  rw [CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor, totalForget]
  exact Grothendieck.functorFromOfEq_congr _ _ _ _ _ _ _ _ h

/-- The localization functor `j_total` of the total site is cocontinuous. This is the
observation which precedes Stacks 0D8B, to which the statement of that lemma refers; it carries
no attribute for the same reason as
`CategoryTheory.SimplicialSemiRepresentable.simplicialSite`. -/
instance totalForget_isCocontinuous :
    (totalForget K).IsCocontinuous ((situation J K).totalTopology) J := by
  rw [← totalAugmentationFunctor_eq J K]
  exact CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor_isCocontinuous
    (augmentation J K)

/-- The localization functor `j_total` of the total site is continuous: the total topology is
generated by the covering families of the individual simplicial degrees, and the restriction of
`j_total` to a degree is `j_c`, which is continuous. This too is the observation which precedes
Stacks 0D8B and carries no attribute. -/
instance totalForget_isContinuous :
    (totalForget K).IsContinuous ((situation J K).totalTopology) J := by
  constructor
  intro G
  refine isSheaf_topologyOfCoverings
    (SimplicialCoverings.total_isSite (slices K) (sliceCoverings J K)
      (simplicialSite J K).isSite (simplicialSite J K).isCocontinuous
      (simplicialSite J K).hasCoverPullbacks) _ ?_
  intro X E hE
  obtain ⟨E', hE', hEeq⟩ : ∃ E'' : PreZeroHypercover.{u} X.fiber,
      sliceCoverings J K X.base ⟨X.fiber, E''⟩ ∧
        E = E''.map (Grothendieck.ι (slices K) X.base) := hE
  subst hEeq
  refine Presieve.isSheafFor_presieve₀_map (Grothendieck.ι (slices K) X.base) _ E' ?_
  have hre : (Grothendieck.ι (slices K) X.base).op ⋙ (totalForget K).op ⋙ G.obj =
      (sliceForget K X.base).op ⋙ G.obj :=
    congrArg (fun F : ((slices K).obj X.base : Cat.{u, u}) ⥤ C => F.op ⋙ G.obj)
      (ι_comp_totalForget K X.base)
  rw [hre]
  exact (Presieve.isSheafFor_iff_generate _).mpr
    ((sliceForget_isContinuous_componentwise J K X.base).op_comp_isSheaf_of_types G _ hE')

/-! ### The morphisms of topoi of the localization functors -/

/-- The morphism of topoi `Sh(C/K_n) ⟶ Sh(C)` of the continuous and cocontinuous localization
functor `j_n`: its inverse image is restriction along `j_n`. -/
noncomputable def localizationMorphism (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf ((situation J K).componentTopology n) (Type u))
      (Sheaf J (Type u)) where
  pushforward := (sliceForget K (op n)).sheafPushforwardCocontinuous (Type u)
    ((situation J K).componentTopology n) J
  inverseImage := (sliceForget K (op n)).sheafPushforwardContinuous (Type u)
    ((situation J K).componentTopology n) J
  adj := (sliceForget K (op n)).sheafAdjunctionCocontinuous (Type u)
    ((situation J K).componentTopology n) J
  preservesFiniteLimits :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ (sliceForget K (op n)) (Type u)

/-- The morphism of topoi `Sh((C/K)_total) ⟶ Sh(C)` of the continuous and cocontinuous
localization functor `j_total`: its inverse image is restriction along `j_total`. -/
noncomputable def totalLocalizationMorphism :
    MorphismOfTopoi (Sheaf ((situation J K).totalTopology) (Type u)) (Sheaf J (Type u)) where
  pushforward := (totalForget K).sheafPushforwardCocontinuous (Type u)
    ((situation J K).totalTopology) J
  inverseImage := (totalForget K).sheafPushforwardContinuous (Type u)
    ((situation J K).totalTopology) J
  adj := (totalForget K).sheafAdjunctionCocontinuous (Type u)
    ((situation J K).totalTopology) J
  preservesFiniteLimits :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ (totalForget K) (Type u)

/-- The special case under `[J.toCoverage.HasPullbacks]` of Stacks 0D8B, whose tag is on
`CategoryTheory.SimplicialSemiRepresentable.stableComponentPushforwardIso` for an arbitrary site.
The morphism of topoi `a_n : Sh(C/K_n) ⟶ Sh(C)` which Stacks 0D70 attaches to the augmentation `j_0`
is the morphism of topoi of the localization functor `j_n`: their direct images agree canonically.

This one is an isomorphism and not an equality. Stacks 0D70 attaches to the augmentation the
composite of the degree-zero morphism of topoi with the transition morphism of a vertex, whose
direct image is a composite of two direct images; the direct image of `j_n` is a single one, for
the composite site functor `C/K_n ⥤ C/K_0 ⥤ C`, which equals `j_n`. Direct images along
cocontinuous functors compose only up to the canonical comparison, which is what this is. -/
noncomputable def componentPushforwardIso (n : SimplexCategory) :
    (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K) (Cat.of C) J
        (situationAugmentation J K) n).pushforward ≅
      (localizationMorphism J K n).pushforward := by
  have h1 : (componentOverMap (K.map (SimplexCategory.const (SimplexCategory.mk 0) n 0).op
      )).IsCocontinuous ((situation J K).componentTopology n)
      ((situation J K).componentTopology (SimplexCategory.mk 0)) :=
    (simplicialSite J K).isCocontinuous _
  have h2 : (sliceForget K (op (SimplexCategory.mk 0))).IsCocontinuous
      ((situation J K).componentTopology (SimplexCategory.mk 0)) J :=
    sliceForget_isCocontinuous J K (SimplexCategory.mk 0)
  have h3 : (componentOverMap (K.map (SimplexCategory.const (SimplexCategory.mk 0) n 0).op) ⋙
      sliceForget K (op (SimplexCategory.mk 0))).IsCocontinuous
      ((situation J K).componentTopology n) J :=
    @CategoryTheory.isCocontinuous_comp _ _ _ _ _ _ _ _
      ((situation J K).componentTopology n)
      ((situation J K).componentTopology (SimplexCategory.mk 0)) J h1 h2
  have h4 : (sliceForget K (op n)).IsCocontinuous ((situation J K).componentTopology n) J :=
    sliceForget_isCocontinuous J K n
  exact (@sheafPushforwardCocontinuousCompIso _ _ _ _ _ _
        ((situation J K).componentTopology n)
        ((situation J K).componentTopology (SimplexCategory.mk 0)) J
        (componentOverMap (K.map (SimplexCategory.const (SimplexCategory.mk 0) n 0).op))
        (sliceForget K (op (SimplexCategory.mk 0))) h1 h2).symm ≪≫
      @SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} _ _ _ _
        ((situation J K).componentTopology n) J _ _ h3 h4
        (slicesMap_comp_sliceForget K (SimplexCategory.const (SimplexCategory.mk 0) n 0).op)

/-- The special case under `[J.toCoverage.HasPullbacks]` of Stacks 0D8B, whose tag is on
`CategoryTheory.SimplicialSemiRepresentable.stableComponentInverseImageIso` for an arbitrary site.
The same identification in inverse images, obtained from uniqueness of left adjoints. -/
noncomputable def componentInverseImageIso (n : SimplexCategory) :
    (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K) (Cat.of C) J
        (situationAugmentation J K) n).inverseImage ≅
      (localizationMorphism J K n).inverseImage :=
  Adjunction.leftAdjointUniq
    (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K) (Cat.of C) J
      (situationAugmentation J K) n).adj
    ((localizationMorphism J K n).adj.ofNatIsoRight (componentPushforwardIso J K n).symm)

/-- Equal cocontinuous site functors have equal direct images: the direct image depends on the
functor and on the proof that it is cocontinuous, and the latter is a proposition. -/
private theorem sheafPushforwardCocontinuous_congr {X Y : Type u} [SmallCategory X]
    [SmallCategory Y] (Jx : GrothendieckTopology X) (Jy : GrothendieckTopology Y) {F G : X ⥤ Y}
    [iF : F.IsCocontinuous Jx Jy] [iG : G.IsCocontinuous Jx Jy] (h : F = G) :
    F.sheafPushforwardCocontinuous (Type u) Jx Jy =
      G.sheafPushforwardCocontinuous (Type u) Jx Jy := by
  subst h
  rfl

/-- The special case under `[J.toCoverage.HasPullbacks]` of Stacks 0D8B, whose tag is on
`CategoryTheory.SimplicialSemiRepresentable.stableTotalPushforward_eq` for an arbitrary site. The
morphism of topoi `a : Sh((C/K)_total) ⟶ Sh(C)` which Stacks 0D70 attaches to the augmentation `j_0`
is the morphism of topoi of the localization functor `j_total`: their direct images are *equal*, not
merely isomorphic, because the cocontinuous functor which Stacks 0D70 attaches to the augmentation
is `j_total` on the nose. -/
theorem totalPushforward_eq :
    (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi
        (augmentation J K)).pushforward = (totalLocalizationMorphism J K).pushforward := by
  exact sheafPushforwardCocontinuous_congr _ _
    (iF := CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor_isCocontinuous
      (augmentation J K))
    (iG := totalForget_isCocontinuous J K) (totalAugmentationFunctor_eq J K)

/-- The identification of direct images of
`CategoryTheory.SimplicialSemiRepresentable.totalPushforward_eq`, read as an isomorphism, which
is the form in which the companion identification of inverse images consumes it. -/
noncomputable def totalPushforwardIso :
    (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi
        (augmentation J K)).pushforward ≅ (totalLocalizationMorphism J K).pushforward := by
  have h1 : (CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor
      (augmentation J K)).IsCocontinuous ((situation J K).totalTopology) J :=
    CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor_isCocontinuous
      (augmentation J K)
  exact @SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} _ _ _ _
    ((situation J K).totalTopology) J _ _ h1 (totalForget_isCocontinuous J K)
    (totalAugmentationFunctor_eq J K)

/-- The special case under `[J.toCoverage.HasPullbacks]` of Stacks 0D8B, whose tag is on
`CategoryTheory.SimplicialSemiRepresentable.stableTotalInverseImageIso` for an arbitrary site. The
same identification in inverse images, obtained from uniqueness of left adjoints. -/
noncomputable def totalInverseImageIso :
    (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi
        (augmentation J K)).inverseImage ≅ (totalLocalizationMorphism J K).inverseImage :=
  Adjunction.leftAdjointUniq
    (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi (augmentation J K)).adj
    ((totalLocalizationMorphism J K).adj.ofNatIsoRight (totalPushforwardIso J K).symm)

end SimplicialSemiRepresentable

end CategoryTheory

end
