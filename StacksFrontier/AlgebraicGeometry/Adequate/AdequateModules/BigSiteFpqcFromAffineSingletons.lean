module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.CoveringSheafCondition
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ProductAlgebra

/-!
# The fpqc sheaf condition on a chosen big site from affine singletons

The final paragraph of [Stacks, Tag 06VL] asserts that an adequate module on a chosen big site
satisfies the sheaf condition for fpqc coverings, and says "details omitted".  This module
supplies those details, in the form of a criterion intrinsic to the site: a presheaf of types on
a chosen big site which is a sheaf for the site's own topology and which descends along every
flat surjective morphism between affine objects *of the site* is a sheaf for the fpqc topology
of the site.

## Main results

* `Stacks.Adequate.isSheaf_fpqc_of_affineSingletons` — **the big-site form of
  [Stacks, Tag 03O1], with no extension hypothesis.**  Its two hypotheses are the sheaf condition
  for `Stacks.Adequate.BigSite.topology` and `Stacks.Adequate.IsAffineSingletonSheaf`, both of
  them conditions on the presheaf of the site alone, and its conclusion is the sheaf condition
  for `Stacks.Adequate.fpqcPrecoverageOn`.

## Implementation notes

The argument follows the proof of Stacks 06VL.  The theorem **supersedes the
extension hypothesis** of `Stacks.Adequate.isSheaf_fpqc_of_exists_extension`: that theorem
reaches the same conclusion by extending the presheaf to all of `Sch/S` and invoking
[Stacks, Tag 03O1] there, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/BigSiteFpqcSheafCriterion.lean` record
why no such extension is available for a presheaf given abstractly.  The present theorem needs
none: the whole argument stays inside the site.

The argument does not reduce the fpqc condition to [Stacks, Tag 03O1]; it runs the reduction
again, inside the site, against the *finest* topology for which `P` is a sheaf,
`CategoryTheory.Sheaf.finestTopologySingle`.  Three steps:

* every object of the site is covered, in the site's own topology, by affine objects — the
  members of its affine cover are open subschemes, hence below the cutoff and again objects of
  the site, and they generate a covering sieve by
  `Stacks.Adequate.sieve_generate_mem_topology_of_coveringMorphismProperty`.  The one-hypercover
  built from that cover reduces a sheaf condition on an arbitrary object to sheaf conditions on
  affine ones;
* a flat surjective morphism of affine objects generates a sieve of the finest topology, because
  its base change along any morphism of the site is again flat and surjective between affines,
  `Stacks.Adequate.BigSite.preservesFiniteLimits_toOver` identifying the fibre product of the
  site with that of the underlying schemes;
* an arbitrary fpqc covering family of an affine object of the site is refined by a single
  morphism from a finite disjoint union of affine opens of its members, which is flat and
  surjective and — by `AlgebraicGeometry.Scheme.size_sigmaObj_lt`, through
  `Stacks.Adequate.BigSite.aleph0_lt_cutoff` and
  `Stacks.Adequate.BigSite.aleph0_lt_cutoff_cof` — again an object of the site.

Every auxiliary declaration is `private` and carries a module-specific prefix: the names of the
source are generic enough (`affineCover`, `liftCover`, …) that a sibling module declaring the
same one would make the two unimportable together.

No `@[stacks]` attribute is attached here; the tag is attached at the assembly site.

## References

* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 03O1](https://stacks.math.columbia.edu/tag/03O1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### Affine covers inside the site -/

/-- A jointly surjective family of open immersions of a chosen big site generates a covering
sieve of the site. -/
private theorem fpqcFromAffSing_sieve₀_mem_topology (B : BigSite τ S) {X : B.category}
    (E : PreZeroHypercover.{w} X)
    (hopen : ∀ i, IsOpenImmersion (B.toOver.map (E.f i)).left)
    (hsurj : ∀ x : X.left.obj, ∃ i, x ∈ Set.range (B.toOver.map (E.f i)).left) :
    E.sieve₀ ∈ B.topology X :=
  sieve_generate_mem_topology_of_coveringMorphismProperty B E.X E.f
    (fun i => isOpenImmersion_le_coveringMorphismProperty τ _ (hopen i)) hsurj

/-- A family of schemes over the scheme underlying an object of a chosen big site, all of whose
members are below the cutoff, read as a family in the site. -/
private def fpqcFromAffSingLiftCover (B : BigSite τ S) (X : B.category)
    (E : PreZeroHypercover.{w} X.left.obj) (hE : ∀ i, (E.X i).size < B.cutoff) :
    PreZeroHypercover.{w} X where
  I₀ := E.I₀
  X i := Over.mk (ObjectProperty.homMk (E.f i ≫ X.hom.hom) :
    (⟨E.X i, hE i⟩ : SchemeBelow B.cutoff) ⟶ ⟨S, B.base_mem⟩)
  f i := Over.homMk (ObjectProperty.homMk (E.f i))

/-- Reading a family of schemes as a family in the site and pushing it back down returns the
family one started with. -/
private theorem fpqcFromAffSingLiftCover_map (B : BigSite τ S) (X : B.category)
    (E : PreZeroHypercover.{w} X.left.obj) (hE : ∀ i, (E.X i).size < B.cutoff) :
    (fpqcFromAffSingLiftCover B X E hE).map (B.toOver ⋙ Over.forget S) = E := by
  cases E
  rfl

/-- The affine cover of an object of a chosen big site: its members are open subschemes of the
total space, hence below the cutoff and again objects of the site. -/
private noncomputable def fpqcFromAffSingAffineCover (B : BigSite τ S) (X : B.category) :
    PreZeroHypercover.{u + 1} X :=
  fpqcFromAffSingLiftCover B X
    ⟨ULift.{u + 1} X.left.obj.affineCover.I₀,
      fun i => X.left.obj.affineCover.X i.down,
      fun i => X.left.obj.affineCover.f i.down⟩
    fun i =>
      Scheme.size_lt_of_isOpenImmersion (X.left.obj.affineCover.f i.down) X.left.property

/-- The affine cover of an object of a chosen big site generates a covering sieve of the
site. -/
private theorem fpqcFromAffSingAffineCover_mem (B : BigSite τ S) (X : B.category) :
    (fpqcFromAffSingAffineCover B X).sieve₀ ∈ B.topology X := by
  refine fpqcFromAffSing_sieve₀_mem_topology B _ (fun i => ?_) (fun x => ?_)
  · exact inferInstanceAs (IsOpenImmersion (X.left.obj.affineCover.f i.down))
  · obtain ⟨i, h⟩ := X.left.obj.affineCover.exists_eq x
    exact ⟨⟨i⟩, h⟩

/-- The one-hypercover of an object of a chosen big site built from the affine cover of the
object and the affine covers of the fibre products of its members. -/
private noncomputable def fpqcFromAffSingOneHypercover (B : BigSite τ S) (X : B.category) :
    B.topology.OneHypercover X :=
  let E := fpqcFromAffSingAffineCover B X
  let F : ∀ i j : E.I₀, PreZeroHypercover.{u + 1} (pullback (E.f i) (E.f j)) := fun i j =>
    fpqcFromAffSingAffineCover B (pullback (E.f i) (E.f j))
  GrothendieckTopology.OneHypercover.mk' (E.refineOneHypercover F)
    (fpqcFromAffSingAffineCover_mem B X) fun i j => by
      have h : (F i j).sieve₀ ∈ B.topology (pullback (E.f i) (E.f j)) :=
        fpqcFromAffSingAffineCover_mem B _
      rwa [← PreZeroHypercover.sieve₁'_refineOneHypercover E F i j] at h

/-- **Affine objects detect the sheaf condition.** A presheaf which is a sheaf for the topology
of a chosen big site is a sheaf for a sieve as soon as it is a sheaf for the pullback of that
sieve to every affine object over the target. -/
private theorem fpqcFromAffSing_isSheafFor_of_affine_pullbacks (B : BigSite τ S)
    (P : B.categoryᵒᵖ ⥤ Type v) (hP : Presieve.IsSheaf B.topology P) {X : B.category}
    (R : Sieve X)
    (h : ∀ {Y : B.category} (f : Y ⟶ X), IsAffine Y.left.obj →
      Presieve.IsSheafFor P (R.pullback f).arrows) :
    Presieve.IsSheafFor P R.arrows :=
  (fpqcFromAffSingOneHypercover B X).isSheafFor_sieve_of_pullback hP
    (fun _ => h _ (inferInstanceAs (IsAffine (Spec _))))
    (fun _ _ _ => (h _ (inferInstanceAs (IsAffine (Spec _)))).isSeparatedFor)

/-! ### Affine singletons in the finest topology -/

/-- **A flat surjective morphism between affine objects of the site is a covering for the finest
topology making `P` a sheaf.** Every base change of such a morphism inside the site is again
flat and surjective between affine objects, the canonical functor of the site preserving fibre
products, so the pullback of the sieve it generates is again a singleton sieve of the same
kind. -/
private theorem fpqcFromAffSing_singleton_mem_finestTopologySingle (B : BigSite τ S)
    (P : B.categoryᵒᵖ ⥤ Type v) (hP : Presieve.IsSheaf B.topology P)
    (ha : IsAffineSingletonSheaf B P) {X Y : B.category} (f : X ⟶ Y)
    (hX : IsAffine X.left.obj) (hY : IsAffine Y.left.obj)
    (hf : Flat (B.toOver.map f).left) (hs : Surjective (B.toOver.map f).left) :
    Sieve.generate (Presieve.singleton f) ∈ Sheaf.finestTopologySingle P Y := by
  have : PreservesFiniteLimits B.toOver := BigSite.preservesFiniteLimits_toOver B
  let G := B.toOver ⋙ Over.forget S
  intro Z g
  apply fpqcFromAffSing_isSheafFor_of_affine_pullbacks B P hP
  intro W a hW
  rw [← Sieve.pullback_comp, ← Sieve.pullbackArrows_comm,
    ← Presieve.isSheafFor_iff_generate, Presieve.pullback_singleton]
  have : IsAffine (G.obj W) := hW
  have : IsAffine (G.obj X) := hX
  have : IsAffine (G.obj Y) := hY
  have sq := (IsPullback.of_hasPullback f (a ≫ g)).map G
  exact ha _ (IsAffine.of_isPullback sq.flip) hW (MorphismProperty.of_isPullback (P := @Flat) sq hf)
    (MorphismProperty.of_isPullback (P := @Surjective) sq hs)

/-- A sieve belongs to a Grothendieck topology as soon as its pullback along every member of a
covering family does. -/
private theorem fpqcFromAffSing_mem_of_covering_pullbacks {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {X : C} (E : PreZeroHypercover.{w} X) (hE : E.sieve₀ ∈ J X)
    (R : Sieve X) (h : ∀ i, R.pullback (E.f i) ∈ J (E.X i)) : R ∈ J X := by
  apply J.transitive hE
  intro Y f hf
  obtain ⟨i, a, rfl⟩ := Sieve.ofArrows.exists hf
  rw [Sieve.pullback_comp]
  exact J.pullback_stable _ (h i)

/-! ### fpqc covering families generate covering sieves of the finest topology -/

/-- A sieve generated by a family `E` is covering as soon as some covering singleton `f` admits a
covering family of its source each of whose members, composed with `f`, factors through `E`. -/
private theorem fpqcFromAffSing_mem_of_factors {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {X Y : C} (E : PreZeroHypercover.{w} X) (f : Y ⟶ X)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J X)
    (T : PreZeroHypercover.{w} Y) (hT : T.sieve₀ ∈ J Y)
    (h : ∀ j, ∃ i, ∃ a : T.X j ⟶ E.X i, T.f j ≫ f = a ≫ E.f i) : E.sieve₀ ∈ J X := by
  apply fpqcFromAffSing_mem_of_covering_pullbacks J (PreZeroHypercover.singleton.{0} f)
    (by
      change Sieve.generate (Presieve.ofArrows _ _) ∈ _
      rwa [Presieve.ofArrows_of_unique]) E.sieve₀
  intro _
  change E.sieve₀.pullback f ∈ J Y
  apply J.superset_covering _ hT
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro j
  obtain ⟨i, a, hw⟩ := h j
  change E.sieve₀ (T.f j ≫ f)
  rw [hw]
  exact E.sieve₀.downward_closed (Sieve.ofArrows_mk _ _ _) a

/-- The morphism out of a coproduct of schemes induced by a jointly surjective family is
surjective. -/
private theorem fpqcFromAffSing_surjective_sigmaDesc {ι : Type u} {X : Scheme.{u}}
    (D : ι → Scheme.{u}) (d : ∀ i, D i ⟶ X) (h : ∀ x, ∃ i, ∃ z, d i z = x) :
    Surjective (Sigma.desc d) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨i, z, hz⟩ := h x
  exact ⟨Sigma.ι D i z, by rwa [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩

/-- A quasi-compact cover of a scheme is refined by finitely many affine opens of its members
whose induced morphism out of their coproduct is surjective. -/
private theorem fpqcFromAffSing_exists_affineOpens_surjective {X : Scheme.{u}}
    [CompactSpace X] (𝒰 : PreZeroHypercover.{v} X) [QuasiCompactCover 𝒰] :
    ∃ (n : ℕ) (s : Fin n → 𝒰.I₀) (V : ∀ k, (𝒰.X (s k)).Opens), (∀ k, IsAffineOpen (V k)) ∧
      Surjective (Sigma.desc fun k : ULift.{u} (Fin n) => (V k.down).ι ≫ 𝒰.f (s k.down)) := by
  obtain ⟨n, s, V, hV, hsurj⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact 𝒰
    (show IsCompact (⊤ : X.Opens).carrier from isCompact_univ)
  refine ⟨n, s, V, hV, fpqcFromAffSing_surjective_sigmaDesc _ _ fun x => ?_⟩
  have hx : x ∈ ⋃ i, 𝒰.f (s i) '' (V i) := hsurj ▸ trivial
  obtain ⟨i, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
  exact ⟨⟨i⟩, ⟨y, hy⟩, hxy⟩

/-- **An fpqc covering family of an affine object of the site is refined by a single flat
surjective morphism from an affine object.** The family is quasi-compact, so finitely many
affine opens of its members already cover the target; their disjoint union is affine, flat and
surjective over the target, and is below the cutoff by
`AlgebraicGeometry.Scheme.size_sigmaObj_lt`, so it is an object of the site. -/
private theorem fpqcFromAffSing_affine_cover_mem (B : BigSite τ S)
    (J : GrothendieckTopology B.category) (hz : B.topology ≤ J)
    (ha : ∀ {X Y : B.category} (f : X ⟶ Y), IsAffine X.left.obj → IsAffine Y.left.obj →
      Flat (B.toOver.map f).left → Surjective (B.toOver.map f).left →
      Sieve.generate (Presieve.singleton f) ∈ J Y)
    {X : B.category} (hX : IsAffine X.left.obj) (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (B.toOver ⋙ Over.forget S)).presieve₀ ∈
      Scheme.fpqcPrecoverage X.left.obj) : E.sieve₀ ∈ J X := by
  classical
  let G := B.toOver ⋙ Over.forget S
  have hXG : IsAffine (G.obj X) := hX
  let 𝒰 : (G.obj X).Cover Scheme.fpqcPrecoverage := ⟨E.map G, hE⟩
  have hqc : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE.1
  have : ∀ i, Flat (𝒰.f i) := ((Scheme.presieve₀_mem_precoverage_iff _).mp hE.2).2
  obtain ⟨n, s, V, hV, hdSurj⟩ :=
    fpqcFromAffSing_exists_affineOpens_surjective 𝒰.toPreZeroHypercover
  let I := ULift.{u} (Fin n)
  let D : I → Scheme.{u} := fun i => (V i.down).toScheme
  let d : ∀ i, D i ⟶ G.obj X := fun i => (V i.down).ι ≫ 𝒰.f (s i.down)
  have hsize (i : I) : (D i).size < B.cutoff :=
    Scheme.size_lt_of_isOpenImmersion (V i.down).ι (E.X (s i.down)).left.property
  have hD : (∐ D).size < B.cutoff :=
    Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff (BigSite.aleph0_lt_cutoff_cof B)
      Cardinal.mk_le_aleph0 D hsize
  let Y : B.category := Over.mk (ObjectProperty.homMk (Sigma.desc d ≫ X.hom.hom) :
    (⟨∐ D, hD⟩ : SchemeBelow B.cutoff) ⟶ ⟨S, B.base_mem⟩)
  let f : Y ⟶ X := Over.homMk (ObjectProperty.homMk (Sigma.desc d))
  have : ∀ i, IsAffine (D i) := fun i => hV i.down
  have hY : IsAffine Y.left.obj := inferInstanceAs (IsAffine (∐ D))
  have _ : IsZariskiLocalAtSource @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  let T' := fpqcFromAffSingLiftCover B Y
    ⟨ULift.{u + 1} I, fun i => D i.down, fun i => Sigma.ι D i.down⟩ fun i => hsize i.down
  have hT' : T'.sieve₀ ∈ B.topology Y := by
    refine fpqcFromAffSing_sieve₀_mem_topology B T' (fun i => ?_) (fun x => ?_)
    · exact inferInstanceAs (IsOpenImmersion (Sigma.ι D i.down))
    · obtain ⟨j, y, hy⟩ := (sigmaOpenCover D).exists_eq x
      exact ⟨⟨j⟩, y, hy⟩
  refine fpqcFromAffSing_mem_of_factors J E f (ha f hY hX (IsZariskiLocalAtSource.sigmaDesc
    (P := @Flat) fun i => inferInstanceAs (Flat ((V i.down).ι ≫ 𝒰.f (s i.down)))) hdSurj)
    T' (hz _ hT') fun j =>
    ⟨s j.down.down, Over.homMk (ObjectProperty.homMk (V j.down.down).ι) ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    exact ((Sigma.ι_comp_desc_assoc d j.down X.hom.hom).trans
      ((Category.assoc (V j.down.down).ι (E.f (s j.down.down)).left.hom X.hom.hom).trans
        (congrArg ((V j.down.down).ι ≫ ·)
          (congrArg (fun g => g.hom) (E.f (s j.down.down)).w)))).symm
  · apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact Sigma.ι_comp_desc d j.down

/-- **Every fpqc covering family of the site generates a covering sieve of the finest topology.**
The affine cover of the target reduces the statement to an affine target, which is
`Stacks.Adequate.fpqcFromAffSing_affine_cover_mem`, the fpqc covering families being stable under
base change. -/
private theorem fpqcFromAffSing_cover_mem (B : BigSite τ S)
    (J : GrothendieckTopology B.category) (hz : B.topology ≤ J)
    (ha : ∀ {X Y : B.category} (f : X ⟶ Y), IsAffine X.left.obj → IsAffine Y.left.obj →
      Flat (B.toOver.map f).left → Surjective (B.toOver.map f).left →
      Sieve.generate (Presieve.singleton f) ∈ J Y)
    {X : B.category} (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (B.toOver ⋙ Over.forget S)).presieve₀ ∈
      Scheme.fpqcPrecoverage X.left.obj) : E.sieve₀ ∈ J X := by
  let G := B.toOver ⋙ Over.forget S
  apply fpqcFromAffSing_mem_of_covering_pullbacks J (fpqcFromAffSingAffineCover B X)
    (hz _ (fpqcFromAffSingAffineCover_mem B X)) E.sieve₀
  intro i
  rw [← Sieve.pullbackArrows_comm, ← PreZeroHypercover.presieve₀_pullback₁]
  apply fpqcFromAffSing_affine_cover_mem B J hz ha (inferInstanceAs (IsAffine (Spec _)))
  rw [PreZeroHypercover.presieve₀_map]
  change (E.pullback₂ ((fpqcFromAffSingAffineCover B X).f i)).presieve₀ ∈
    Scheme.fpqcPrecoverage.comap G _
  rw [PreZeroHypercover.presieve₀_pullback₁]
  apply Precoverage.pullbackArrows_mem
  change E.presieve₀.map G ∈ Scheme.fpqcPrecoverage (G.obj X)
  rwa [← PreZeroHypercover.presieve₀_map]

/-! ### The criterion -/

/-- **[Stacks, Tag 03O1] on a chosen big site, with no extension hypothesis.** A presheaf of
types on a chosen big site over `S` which is a sheaf for the topology of the site and which
descends along every flat surjective morphism between affine objects of the site satisfies the
sheaf condition for every fpqc covering family of the site.

This is the criterion the final paragraph of [Stacks, Tag 06VL] uses, for which the source says
"details omitted".  Both hypotheses are intrinsic to the presheaf of the site, so this
supersedes `Stacks.Adequate.isSheaf_fpqc_of_exists_extension`, which reaches the same conclusion
only for a presheaf admitting an extension to the schemes over `S`. -/
public theorem isSheaf_fpqc_of_affineSingletons (B : BigSite τ S) (P : B.categoryᵒᵖ ⥤ Type v)
    (hP : Presheaf.IsSheaf B.topology P) (ha : IsAffineSingletonSheaf B P) :
    Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck P := by
  rw [isSheaf_iff_isSheaf_of_type] at hP ⊢
  let J := Sheaf.finestTopologySingle P
  have hz : B.topology ≤ J := fun X R hR Y f => hP _ (B.topology.pullback_stable f hR)
  have hle : (fpqcPrecoverageOn B).toGrothendieck ≤ J := by
    rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro X R hR
    obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
    apply fpqcFromAffSing_cover_mem B J hz
      (fpqcFromAffSing_singleton_mem_finestTopologySingle B P hP ha) ⟨ι, Z, f⟩
    rwa [PreZeroHypercover.presieve₀_map]
  apply Presieve.isSheaf_of_le P hle
  intro X R hR
  simpa only [Sieve.pullback_id] using hR X (𝟙 X)

end Stacks.Adequate

end
