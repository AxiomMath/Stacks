module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiGermSections
import StacksCore.Tactic.StacksAttribute

/-!
# The germ-model sections presheaf is a sheaf

Let `X'` be an object of the locally quasi-compact Zariski site and let `F` be a sheaf of sets on
its space. The germ-model sections presheaf `germSectionsPresheaf S X' F` of
`ZariskiProperBaseChangeReduction.lean` assigns to an object `h : W ⟶ X'` of the localized site
the global sections `Γ(W, h^{-1}F)` of the germ-model inverse image, and its restriction maps are
literally precomposition. This file proves that it is a sheaf for the localized Zariski topology,
so that the right-hand side of the sections formula of Stacks 09X3 is an object of the topos
`Sh(LC_Zar/X')` and not merely a presheaf.

The proof is the classical gluing argument for continuous sections of a fixed space of germs. A
covering sieve `R` of `h : W ⟶ X'` contains, by
`CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`, a Zariski
covering family `m_i : V_i ⟶ W` — open embeddings of the site which are jointly surjective. Each
member of an `R`-compatible family is a germ section over `V_i`, and
`exists_germSections_of_isOpenEmbedding` transports it to a germ section over the open
`O_i = m_i(V_i)` of `W`; these agree on overlaps, so `GermPullback.exists_glue` glues them.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.germSectionsSheaf`: the germ-model sections
  presheaf, as a sheaf of sets on the localized Zariski site.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_germSections_of_isOpenEmbedding`: a
  germ section over the whole of a space maps, along an open embedding of that space, to a germ
  section over the image of the embedding.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_factor_of_range_subset`: a morphism
  of the site whose image lies inside the image of an open embedding of the site factors through
  it.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isSheaf_germSectionsPresheaf`: the
  germ-model sections presheaf is a sheaf for the localized Zariski topology.

## Implementation notes

Two germ sections of the compatible family are compared not over a fibre product of the site but
over an *open* of a space of the site, cut out as the preimage of the image of one of the open
embeddings and realised as an object of the site by `opensToSlice`: the points of such an object
are known, which is what the pointwise comparison of germ sections needs, whereas identifying the
points of a fibre product of the site would need the fibre-product comparison of Stacks 0D90.
This is also why a morphism of the sieve which is *not* an open embedding causes no trouble: only
the second of the two arrows being compared is ever required to be one.

Extracting a Zariski covering family from a covering sieve needs the Zariski precoverage to have
isomorphisms, pullbacks, and stability under composition and base change. All four are inherited
from the open-embedding precoverage of `TopCat`, which is why the proof first arranges that the
inclusion of the bounded subcategory into `TopCat` preserves fibre products, exactly as in
`opensToSlice_isCocontinuous`.

## References

* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- **Germ sections transport along an open embedding.** Let `e : Z' → Z` be an open embedding
and let `p : Z → Y` and `p' : Z' → Y` be maps with `p' = p ∘ e`. A section of the germ model
`p'^{-1}𝒢` over the whole of `Z'` determines a section of `p^{-1}𝒢` over the open `e(Z')` of `Z`,
whose value at `e z` is the value of the given section at `z`.

A germ section is a function to the total space of germs of `𝒢` which is locally the family of
germs of a section of `𝒢`, and the total space does not mention the structure map; so the
transported section is just the given one read through the inverse of `e`, and the local
condition transports because `e` is an open map. -/
lemma exists_germSections_of_isOpenEmbedding {Y Z Z' : TopCat.{u}} {𝒢 : Y.Presheaf (Type (max u t))}
    {p : Z → Y} {p' : Z' → Y} {e : Z' → Z} (he : Topology.IsOpenEmbedding e)
    (hcomp : ∀ z, p' z = p (e z))
    (σ : (GermPullback.sheaf p' 𝒢).presheaf.obj (op ⊤)) :
    ∃ τ : (GermPullback.sheaf p 𝒢).presheaf.obj (op ⟨Set.range e, he.isOpen_range⟩),
      ∀ z : Z', τ.1 ⟨e z, ⟨z, rfl⟩⟩ = σ.1 ⟨z, trivial⟩ := by
  classical
  set O : Opens Z := ⟨Set.range e, he.isOpen_range⟩
  have hmem : ∀ z : O, ∃ y : Z', e y = z.1 := fun z => z.2
  choose pick hpick using hmem
  have hpick_eq : ∀ (z : O) (y : Z'), e y = z.1 → pick z = y := fun z y h =>
    he.injective ((hpick z).trans h.symm)
  refine ⟨⟨fun z => σ.1 ⟨pick z, trivial⟩, fun z => ?_⟩, fun y => ?_⟩
  · obtain ⟨A₀, hyA₀, i, V₀, hV₀, s, hs⟩ :=
      GermPullback.exists_repr σ (trivial : pick z ∈ (⊤ : Opens Z'))
    have hBopen : IsOpen (e '' (A₀ : Set Z')) := he.isOpenMap _ A₀.isOpen
    set B₀ : Opens Z := ⟨e '' (A₀ : Set Z'), hBopen⟩
    have hBO : B₀ ≤ O := by
      rintro a ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    have hrepr : ∀ w : B₀, ∃ y : Z', y ∈ A₀ ∧ e y = w.1 := fun w => w.2
    have hV : ∀ w : B₀, p w.1 ∈ V₀ := by
      intro w
      obtain ⟨y, hy, hw⟩ := hrepr w
      rw [← hw, ← hcomp y]
      exact hV₀ ⟨y, hy⟩
    refine ⟨B₀, ⟨pick z, hyA₀, hpick z⟩, homOfLE hBO, V₀, hV, s, fun w => ?_⟩
    obtain ⟨y, hy, hw⟩ := hrepr w
    have hpw : pick ((homOfLE hBO) w) = y := hpick_eq _ y hw
    exact (congrArg σ.1 (Subtype.ext hpw)).trans ((hs ⟨y, hy⟩).trans
      (GermPullback.Germs.mk_eq_mk s ((hcomp y).trans (congrArg p hw)) _ _))
  · exact congrArg σ.1 (Subtype.ext (hpick_eq ⟨e y, ⟨y, rfl⟩⟩ y rfl))

/-- **A morphism of the site factors through an open embedding covering its image.** If `b` is a
morphism of the site whose underlying map is an open embedding, then any morphism `a` of the site
with the same target whose image is contained in the image of `b` factors as `a = c ≫ b`. The
underlying map of `c` is the set-theoretic lift, which is continuous because `b` is an embedding
and lands in the site because the inclusion of the site into `TopCat` is fully faithful. -/
lemma exists_factor_of_range_subset
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {A B C : S.category}
    (a : A ⟶ C) (b : B ⟶ C) (hb : Topology.IsOpenEmbedding ((siteToTop S).map b))
    (hsub : Set.range ((siteToTop S).map a) ⊆ Set.range ((siteToTop S).map b)) :
    ∃ c : A ⟶ B, c ≫ b = a := by
  classical
  have hmem : ∀ z : (siteToTop S).obj A, ∃ y, ((siteToTop S).map b) y = ((siteToTop S).map a) z :=
    fun z => hsub ⟨z, rfl⟩
  choose φ hφ using hmem
  have hcont : Continuous φ := by
    refine hb.isInducing.continuous_iff.mpr ?_
    rw [show (fun y => ((siteToTop S).map b) y) ∘ φ = fun z => ((siteToTop S).map a) z from
      funext hφ]
    exact (ConcreteCategory.hom ((siteToTop S).map a)).continuous
  refine ⟨(siteToTop S).preimage (TopCat.ofHom ⟨φ, hcont⟩), (siteToTop S).map_injective ?_⟩
  rw [Functor.map_comp, Functor.map_preimage]
  exact ConcreteCategory.hom_ext _ _ hφ

/-- The inclusion of the locally quasi-compact Zariski site into `TopCat` preserves fibre
products, because the bounded subcategory of `LocallyQuasiCompactHausdorff` is closed under
countable limits. -/
lemma preservesLimitsOfShape_walkingCospan_siteToTop
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) :
    PreservesLimitsOfShape WalkingCospan (siteToTop S) := by
  let Q : ObjectProperty LocallyQuasiCompactHausdorff := fun Y => lcSize Y < S.qcSite.cutoff
  let J' := ULiftHom.{u} (ULift.{u} WalkingCospan)
  let eShape : WalkingCospan ≌ J' := ULiftHomULiftCategory.equiv WalkingCospan
  let _ : HasLimitsOfShape J' LocallyQuasiCompactHausdorff := hasLimitsOfShape_of_equivalence eShape
  let _ : Q.IsClosedUnderLimitsOfShape J' :=
    S.qcSite.boundedSubcategory.closedUnderCountableLimits J'
  let _ : PreservesLimitsOfShape WalkingCospan S.qcSite.inclusion :=
    preservesLimitsOfShape_of_equiv eShape.symm S.qcSite.inclusion
  exact comp_preservesLimitsOfShape S.qcSite.inclusion locallyQuasiCompactHausdorffToTop

/-- **A covering sieve of the localized Zariski site contains a covering family.** A sieve
covering an object `W` of `LC_Zar/X'` contains a family of morphisms of the site to `W.left`
which are open embeddings of spaces and are jointly surjective. This is the input to the gluing
argument, and extracting it is what needs the Zariski precoverage to have isomorphisms,
pullbacks, and stability under composition and base change. -/
lemma exists_isOpenEmbedding_family_of_mem_zariskiTopology_over
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X' : S.category} {W : Over X'}
    {R : Sieve W} (hR : R ∈ (S.zariskiTopology.over X') W) :
    ∃ (ι : Type (u + 1)) (Z : ι → S.category) (g : ∀ i, Z i ⟶ W.left),
      (∀ i, Topology.IsOpenEmbedding ((siteToTop S).map (g i))) ∧
        (∀ y : (siteToTop S).obj W.left, ∃ i, y ∈ Set.range ((siteToTop S).map (g i))) ∧
          ∀ i, R (Over.homMk (g i) : Over.mk (g i ≫ W.hom) ⟶ W) := by
  have := preservesLimitsOfShape_walkingCospan_siteToTop S
  have hR' : Sieve.overEquiv W R ∈ (TopCat.precoverage.comap
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop)).toGrothendieck W.left :=
    (S.zariskiTopology.mem_over_iff R).mp hR
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR'
  obtain ⟨T, hT, hTle⟩ := hR'
  obtain ⟨ι, Z, g, hTrep⟩ := T.exists_eq_ofArrows
  rw [hTrep] at hT hTle
  obtain ⟨hjoint, hopen⟩ : Presieve.map (siteToTop S) (Presieve.ofArrows Z g) ∈
      TopCat.precoverage ((siteToTop S).obj W.left) := hT
  have hopen' :
      Presieve.ofArrows (fun i => (siteToTop S).obj (Z i)) (fun i => (siteToTop S).map (g i)) ∈
        TopCat.isOpenEmbedding.precoverage ((siteToTop S).obj W.left) := by
    simpa using hopen
  have hopenMap : ∀ i, Topology.IsOpenEmbedding ((siteToTop S).map (g i)) := by
    simpa [TopCat.isOpenEmbedding] using (MorphismProperty.ofArrows_mem_precoverage.mp hopen')
  have hjoint' : ∀ y : (siteToTop S).obj W.left,
      ∃ i, y ∈ Set.range ((siteToTop S).map (g i)) := by
    have hjoint'' :
        Presieve.ofArrows (fun i => (siteToTop S).obj (Z i)) (fun i => (siteToTop S).map (g i)) ∈
          Types.jointlySurjectivePrecoverage.comap (forget TopCat) ((siteToTop S).obj W.left) := by
      simpa only [Presieve.map_ofArrows] using hjoint
    simpa using (Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff
      (F := forget TopCat) (Y := fun i => (siteToTop S).obj (Z i))
      (f := fun i => (siteToTop S).map (g i))).mp hjoint''
  exact ⟨ι, Z, g, hopenMap, hjoint', fun i =>
    (Sieve.overEquiv_iff R (g i)).mp (hTle _ (g i) (Presieve.ofArrows.mk i))⟩

/-- **Two members of a compatible family of germ sections agree where their images meet.** Let
`x` be a compatible family of germ sections for a sieve `R` on an object `W` of the localized
Zariski site and let `m : W' ⟶ W` and `k : W'' ⟶ W` be members of `R`, the first of which has an
open embedding of spaces as underlying map. Then the members of `x` at `m` and at `k` take the
same value at points of `W'.left` and of `W''.left` with the same image in `W.left`.

Only the first of the two arrows has to be an open embedding: the two values are compared over
the preimage in `W''.left` of the image of `m`, realised as an object of the site by
`opensToSlice`, through which the restriction of `k` factors because `m` is an open embedding. -/
lemma germSections_apply_eq_of_map_eq
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X' : S.category}
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) {W : Over X'}
    {R : Sieve W} {x : Presieve.FamilyOfElements (germSectionsPresheaf S X' F) R.arrows}
    (hx : x.Compatible) {W' W'' : Over X'} {m : W' ⟶ W} {k : W'' ⟶ W} (hm : R m) (hk : R k)
    (hopen : Topology.IsOpenEmbedding ((siteToTop S).map m.left))
    (y : (siteToTop S).obj W'.left) (z : (siteToTop S).obj W''.left)
    (hyz : ((siteToTop S).map m.left) y = ((siteToTop S).map k.left) z) :
    (x m hm).1 ⟨y, trivial⟩ = (x k hk).1 ⟨z, trivial⟩ := by
  let U : Opens ((siteToTop S).obj W''.left) :=
    ⟨((siteToTop S).map k.left) ⁻¹' Set.range ((siteToTop S).map m.left),
      hopen.isOpen_range.preimage
        (ConcreteCategory.hom ((siteToTop S).map k.left)).continuous⟩
  let D := (S.opensToSlice W''.left).1.obj U
  have hDrange : Set.range ((siteToTop S).map D.hom) = U.1 :=
    ((S.opensToSlice W''.left).2 U).2
  obtain ⟨d, hd⟩ : ∃ d, ((siteToTop S).map D.hom) d = z := hDrange.symm.subset ⟨y, hyz⟩
  have hsub : Set.range ((siteToTop S).map (D.hom ≫ k.left)) ⊆
      Set.range ((siteToTop S).map m.left) := by
    rintro p ⟨d', rfl⟩
    rw [Functor.map_comp, ConcreteCategory.comp_apply]
    exact hDrange.subset ⟨d', rfl⟩
  obtain ⟨c, hc⟩ := exists_factor_of_range_subset S (D.hom ≫ k.left) m.left hopen hsub
  have hc' : c ≫ W'.hom = D.hom ≫ W''.hom := by
    rw [← Over.w m, ← Category.assoc, hc, Category.assoc, Over.w k]
  have hcomm : (Over.homMk c hc' : Over.mk (D.hom ≫ W''.hom) ⟶ W') ≫ m =
      (Over.homMk D.hom : Over.mk (D.hom ≫ W''.hom) ⟶ W'') ≫ k :=
    Over.OverMorphism.ext (by simpa using hc)
  have h1 := congrArg (fun σ : (germSectionsPresheaf S X' F).obj
    (op (Over.mk (D.hom ≫ W''.hom))) => σ.1 ⟨d, trivial⟩) (hx _ _ hm hk hcomm)
  simp only [germSectionsPresheaf_map_val, unop_op] at h1
  have hcd : ((siteToTop S).map c) d = y := by
    refine hopen.injective ?_
    have h2 := ConcreteCategory.congr_hom (congrArg (siteToTop S).map hc) d
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at h2
    rwa [hyz, ← hd]
  rwa [← hcd, ← hd]

/-- **A germ section is read off from its restriction along a morphism of the site.** If the
restriction of a germ section `ρ` over `W` along `m : W' ⟶ W` is `σ`, then the value of `ρ` at a
point in the image of `m` is the value of `σ` at any preimage of that point. -/
lemma germSections_apply_eq_of_restrict_eq
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X' : S.category}
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) {W W' : Over X'}
    {m : W' ⟶ W} {ρ : (germSectionsPresheaf S X' F).obj (op W)}
    {σ : (germSectionsPresheaf S X' F).obj (op W')}
    (h : (germSectionsPresheaf S X' F).map m.op ρ = σ)
    {y : (siteToTop S).obj W'.left} {z : (⊤ : Opens ((siteToTop S).obj W.left))}
    (hy : ((siteToTop S).map m.left) y = z.1) :
    ρ.1 z = σ.1 ⟨y, trivial⟩ :=
  (congrArg ρ.1 (Subtype.ext hy.symm)).trans
    (congrArg (fun σ' : (germSectionsPresheaf S X' F).obj (op W') => σ'.1 ⟨y, trivial⟩) h)

/-- **The germ-model sections presheaf is a sheaf.** The presheaf on the localized Zariski site
`LC_Zar/X'` whose sections over `h : W ⟶ X'` are the global sections of the germ-model inverse
image `h^{-1}F` satisfies the sheaf condition for the localized Zariski topology: an open covering
of `W` by objects of the site and a family of germ sections agreeing on the overlaps determine a
unique germ section on `W`. This is the first assertion of Stacks 09X3. -/
@[stacks 09X3 "the Zariski sheaf condition"]
theorem isSheaf_germSectionsPresheaf
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    Presheaf.IsSheaf (S.zariskiTopology.over X') (germSectionsPresheaf S X' F) := by
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  intro W R hR x hx
  obtain ⟨ι, Z, g, hopenMap, hjoint', hRg⟩ :=
    exists_isOpenEmbedding_family_of_mem_zariskiTopology_over S hR
  have hcompat : ∀ (i : ι) (z : (siteToTop S).obj (Z i)),
      ((siteToTop S).map (Over.mk (g i ≫ W.hom)).hom) z =
        ((siteToTop S).map W.hom) (((siteToTop S).map (g i)) z) :=
    fun i => siteToTop_hom_apply S (Over.homMk (g i) : Over.mk (g i ≫ W.hom) ⟶ W)
  let xa : ∀ i : ι, (germSectionsPresheaf S X' F).obj (op (Over.mk (g i ≫ W.hom))) :=
    fun i => x (Over.homMk (g i)) (hRg i)
  choose τ hτ using fun i : ι => exists_germSections_of_isOpenEmbedding (𝒢 := F.1)
    (p := ⇑((siteToTop S).map W.hom)) (hopenMap i) (hcompat i) (xa i)
  have hτ' : ∀ (i : ι) (yi : (siteToTop S).obj (Z i)) (z : (siteToTop S).obj W.left)
      (hyi : ((siteToTop S).map (g i)) yi = z), (τ i).1 ⟨z, yi, hyi⟩ = (xa i).1 ⟨yi, trivial⟩ :=
    fun i yi _ hyi => (congrArg (τ i).1 (Subtype.ext hyi.symm)).trans (hτ i yi)
  have hagree : ∀ (i j : ι) (z : (siteToTop S).obj W.left)
      (hz : z ∈ (⟨Set.range ((siteToTop S).map (g i)), (hopenMap i).isOpen_range⟩ :
        Opens ((siteToTop S).obj W.left)))
      (hz' : z ∈ (⟨Set.range ((siteToTop S).map (g j)), (hopenMap j).isOpen_range⟩ :
        Opens ((siteToTop S).obj W.left))),
      (τ i).1 ⟨z, hz⟩ = (τ j).1 ⟨z, hz'⟩ := by
    intro i j z hz hz'
    obtain ⟨yi, hyi⟩ := hz
    obtain ⟨yj, hyj⟩ := hz'
    exact (hτ' i yi z hyi).trans ((germSections_apply_eq_of_map_eq S F hx (hRg i) (hRg j)
      (hopenMap i) yi yj (hyi.trans hyj.symm)).trans (hτ' j yj z hyj).symm)
  obtain ⟨ρ, hρ⟩ := GermPullback.exists_glue (𝒢 := F.1) (g := ⇑((siteToTop S).map W.hom))
    (W := ⊤) (fun i : ι => (⟨Set.range ((siteToTop S).map (g i)), (hopenMap i).isOpen_range⟩ :
      Opens ((siteToTop S).obj W.left)))
    (fun _ => le_top) (fun z _ => hjoint' z) τ hagree
  have hamalg : x.IsAmalgamation (ρ : (germSectionsPresheaf S X' F).obj (op W)) := by
    refine fun W'' k hk => GermPullback.ext fun z => ?_
    obtain ⟨i, yi, hyi⟩ := hjoint' (((siteToTop S).map k.left) z.1)
    exact ((hρ i _ ⟨yi, hyi⟩).trans (hτ' i yi _ hyi)).trans
      (germSections_apply_eq_of_map_eq S F hx (hRg i) hk (hopenMap i) yi z.1 hyi)
  refine ⟨ρ, hamalg, fun ρ' hρ' => GermPullback.ext fun z => ?_⟩
  obtain ⟨i, yi, hyi⟩ := hjoint' z.1
  exact (germSections_apply_eq_of_restrict_eq S F (hρ' _ (hRg i)) hyi).trans
    (germSections_apply_eq_of_restrict_eq S F (hamalg _ (hRg i)) hyi).symm

/-- **The germ-model sections sheaf, the right-hand side of the sections formula of Stacks
09X3.** For a sheaf of sets `F` on the space of an object `X'` of the site, this is
`germSectionsPresheaf S X' F` — the presheaf `(h : W ⟶ X') ↦ Γ(W, h^{-1}F)` on the localized
Zariski site `LC_Zar/X'` — together with the proof that it is a sheaf. -/
def germSectionsSheaf
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    Sheaf (S.zariskiTopology.over X') (Type (max u t)) :=
  ⟨germSectionsPresheaf S X' F, isSheaf_germSectionsPresheaf S X' F⟩

/-- The underlying presheaf of `germSectionsSheaf` is `germSectionsPresheaf`. -/
@[simp]
lemma germSectionsSheaf_obj
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    (germSectionsSheaf S X' F).1 = germSectionsPresheaf S X' F := rfl

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
