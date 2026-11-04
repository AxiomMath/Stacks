module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCover
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSubsite

/-!
# The affine objects are enough to test the sheaf condition

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids and give `𝒳` the topology it
inherits from the big fppf site over `S`.  Every object of `𝒳` carries a covering family whose
members are affine: an affine open cover of the underlying scheme is an fppf covering family of
the big site, and its members lift along `p`.  Consequently the arrows of a covering sieve whose
source is affine already generate a covering sieve, and a presheaf on `𝒳` — or on any of its
slices — which satisfies the sheaf condition for the covering families by affine objects is a
sheaf.  Over an affine object, where covering sieves contain finite covering families, the
testing family may in addition be taken finite.

This is the comparison step the computation of the sections of a quasi-coherent module needs:
the sheaf condition is only available for particular coverings — a single faithfully flat
morphism between affine objects, where the Amitsur complex computes it — while the module whose
sections are wanted is a sheaf for the whole inherited topology, at objects which need not be
affine.  The three results below are what bridge the two: a non-affine object is handled
Zariski-locally, a covering of an affine object is cut down to a finite affine family, and the
general criterion assembles the two into the sheaf condition for the topology.

## Main definitions

* `AlgebraicGeometry.FibredSite.affinePrecoverage` and
  `AlgebraicGeometry.FibredSite.affinePrecoverageOver`: the covering families all of whose
  members have affine source, on the associated fppf site and on its slice at an object.

## Main results

* `AlgebraicGeometry.FibredSite.exists_affine_ofArrows` and
  `AlgebraicGeometry.FibredSite.exists_affine_ofArrows_over`: **every object of the associated
  fppf site, and of each of its slices, carries a covering family by affine objects.**
* `AlgebraicGeometry.FibredSite.generates_affinePrecoverage` and
  `AlgebraicGeometry.FibredSite.generates_affinePrecoverageOver`: **those families generate the
  topology**, in the sense of `CategoryTheory.Precoverage.Generates`.
* `AlgebraicGeometry.FibredSite.isSheaf_of_isSheafFor_affine` and
  `AlgebraicGeometry.FibredSite.isSheaf_over_of_isSheafFor_affine`: **a presheaf which satisfies
  the sheaf condition for the covering families by affine objects is a sheaf.**
* `AlgebraicGeometry.FibredSite.exists_finite_affine_ofArrows_le_over`: **a covering sieve of an
  affine object of a slice contains a finite covering family of affine objects.**
* `CategoryTheory.GrothendieckTopology.exists_finite_ofArrows_le`: the site-level statement
  behind the last one.
* `AlgebraicGeometry.Scheme.mem_fppfPrecoverage_of_forall_eq_comp` and
  `AlgebraicGeometry.Scheme.mem_fppfPrecoverage_of_equiv`: membership in the fppf precoverage of
  schemes is unchanged by composing the members of a family with isomorphisms of their sources and
  by reindexing the family.
* `AlgebraicGeometry.BigFppfSite.exists_fppf_ofArrows_le`,
  `AlgebraicGeometry.BigFppfOver.exists_fppf_ofArrows_le_baseOverTopology` and
  `AlgebraicGeometry.FibredSite.exists_fppf_ofArrows_le`: **a covering sieve of a big fppf site, of
  the big fppf category over a scheme, or of the associated site of a category fibred in groupoids
  contains a family whose image in schemes is an fppf covering family.**
* `AlgebraicGeometry.FibredSite.exists_affine_fppf_ofArrows`: the covering family by affine objects
  of `AlgebraicGeometry.FibredSite.exists_affine_ofArrows` **is fppf in schemes.**
* `AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le` and
  `AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le_over`: **a covering sieve of
  an affine object, of the associated site or of one of its slices, contains a finite family of
  affine objects which is an fppf covering family in schemes.**

## Implementation notes

`AlgebraicGeometry.FibredSite.coversTop_affineObj` records that the affine objects cover the
final object; its proof produces, at every object, exactly the covering family
`AlgebraicGeometry.FibredSite.exists_affine_ofArrows` asserts to exist, but the conclusion it
keeps — that the sieve of the arrows whose *source* admits a morphism to an affine object covers
— is weaker, and does not factor an arrow through an affine object.  The construction is
therefore repeated here in the form the refinement argument consumes.

The slice statements are obtained from the statements on `𝒳` by the correspondence between
covering sieves of `CategoryTheory.Over.mk f` and covering sieves of its underlying object,
`CategoryTheory.GrothendieckTopology.mem_over_iff`, exactly as in
`AlgebraicGeometry.BigFppfOver.hasFiniteSubcovering_over`.

The refinements are stated twice, once without the fppf condition of the refined family and once
with it.  The sheaf-condition arguments which consume the first form never look at the morphisms
of the family, so adding a conjunct to them would only burden their callers; descent along the
family does look at them, since the ring map a member induces on global functions is faithfully
flat exactly because the member is flat and the family is jointly surjective.  The two forms share
no proof: the fppf condition is carried by the selected covering families of the big site and by
the affine open covers the refinements are built from, and recording it means following it through
the lifts along the structure functor, where a lift is only determined up to the isomorphism of
sources it comes with.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0D05](https://stacks.math.columbia.edu/tag/0D05)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (Q : C → Prop)
  (hQ : ∀ X : C, ∃ (I : Type w) (Y : I → C) (g : ∀ i, Y i ⟶ X),
    (∀ i, Q (Y i)) ∧ Sieve.ofArrows Y g ∈ J X)

include hQ

/-- **Over an object with the finite subcovering property, every covering sieve contains a finite
covering family whose sources satisfy `Q`**, provided the objects satisfying `Q` cover every
object.  The arrows of the sieve with source satisfying `Q` generate a covering sieve, a finite
subfamily of that one still covers, and each of its members factors through one of the retained
arrows; the arrows factored through form the required family. -/
theorem exists_finite_ofArrows_le {X : C} (hX : J.HasFiniteSubcovering X) (S : Sieve X)
    (hS : S ∈ J X) :
    ∃ (n : ℕ) (Y : Fin n → C) (g : ∀ i, Y i ⟶ X), (∀ i, Q (Y i)) ∧ (∀ i, S (g i)) ∧
      Sieve.ofArrows Y g ∈ J X := by
  obtain ⟨n, Z, c, hcS, hccov⟩ := hX _ (generate_restrictToObjects_mem J Q hQ S hS)
  choose Y h g hg hfac using hcS
  refine ⟨n, Y, g, fun i => (hg i).2, fun i => (hg i).1, J.superset_covering ?_ hccov⟩
  intro W a ha
  rw [Sieve.mem_ofArrows_iff] at ha
  obtain ⟨i, b, rfl⟩ := ha
  exact ⟨Y i, b ≫ h i, g i, Presieve.ofArrows.mk i, by rw [Category.assoc, hfac i]⟩

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.FibredSite

/-- The image in schemes of a selected covering family is an fppf covering family. -/
private theorem _root_.AlgebraicGeometry.BigFppfSite.ofArrows_inclusion_mem_fppfPrecoverage
    (B : BigFppfSite.{u}) {T : B.Schemes} {E : PreZeroHypercover.{u + 1} T}
    (hE : B.IsCovering ⟨T, E⟩) :
    Presieve.ofArrows (fun i => B.inclusion.obj (E.X i)) (fun i => B.inclusion.map (E.f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T) := by
  have h := hE.1
  rwa [IsFppfCovering, Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map,
    PreZeroHypercover.presieve₀] at h

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- A morphism into the image of an object of a category fibred in groupoids lifts to a morphism
whose image is that morphism up to an equality of sources. -/
private theorem exists_lift_map_eq_eqToHom_comp (hp : p.IsFiberedInGroupoids) {w : 𝒳}
    {X : BigFppfOver B S hS} (c : X ⟶ p.obj w) :
    ∃ (z : 𝒳) (ψ : z ⟶ w) (h : p.obj z = X), p.map ψ = eqToHom h ≫ c := by
  obtain ⟨z, ψ, hψ⟩ := hp.exists_lift c w rfl
  refine ⟨z, ψ, IsHomLift.domain_eq p c ψ, ?_⟩
  simpa using IsHomLift.fac' p c ψ

/-- Every object of the associated fppf site carries a covering family by affine objects which
is, up to equalities of sources, the image of a covering family of the big site whose image in
schemes is fppf. -/
private theorem exists_affine_ofArrows_aux (hp : p.IsFiberedInGroupoids) (W : 𝒳) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳) (φ : ∀ j, y j ⟶ W),
      (∀ j, IsAffineOver B S hS (p.obj (y j))) ∧
        Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS p .fppf W ∧
        ∃ (X : I → BigFppfOver B S hS) (g : ∀ j, X j ⟶ p.obj W) (hdom : ∀ j, p.obj (y j) = X j),
          (∀ j, p.map (φ j) = eqToHom (hdom j) ≫ g j) ∧
            Presieve.ofArrows (fun j => (BigFppfOver.toScheme B S hS).obj (X j))
                (fun j => (BigFppfOver.toScheme B S hS).map (g j)) ∈
              Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj W)) := by
  classical
  obtain ⟨V, hV, hVU⟩ := exists_isCovering_tautologicallyEquivalent_openCover B
    (p.obj W).left (B.inclusion.obj (p.obj W).left).affineOpenCover.openCover
  obtain ⟨-, β, hβ⟩ := hVU
  have hVaff : ∀ j, IsAffine (B.inclusion.obj (V.X j)) := by
    intro j
    obtain ⟨e, -⟩ := hβ j
    have : IsAffine
        ((B.inclusion.obj (p.obj W).left).affineOpenCover.openCover.X (β j)) := by
      show IsAffine (Spec ((B.inclusion.obj (p.obj W).left).affineOpenCover.X (β j)))
      exact isAffine_Spec _
    have hIso : IsIso e.hom := e.isIso_hom
    exact @IsAffine.of_isIso _ _ e.hom hIso inferInstance
  let Vobj (j : V.I₀) : BigFppfOver B S hS := Over.mk (V.f j ≫ (p.obj W).hom)
  let vmap (j : V.I₀) : Vobj j ⟶ p.obj W := Over.homMk (V.f j)
  have hBcover : Sieve.ofArrows Vobj vmap ∈
      BigFppfOver.baseOverTopology B S hS .fppf (p.obj W) := by
    show Sieve.ofArrows Vobj vmap ∈ (B.topology.over (B.obj hS)) (p.obj W)
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    show Sieve.ofArrows V.X V.f ∈ B.topology (p.obj W).left
    have hpre : V.presieve₀ ∈ B.precoverage (p.obj W).left := ⟨V, rfl, hV⟩
    simpa [PreZeroHypercover.presieve₀] using Precoverage.generate_mem_toGrothendieck hpre
  choose y φ hdom hmapφ using fun j => exists_lift_map_eq_eqToHom_comp B S hS p hp (vmap j)
  have hcart : ∀ j, p.IsStronglyCartesian (p.map (φ j)) (φ j) :=
    fun j => hp.isStronglyCartesian (φ j)
  have hvmapmem : ∀ j, (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)) (vmap j) :=
    fun j => (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, eqToHom (hdom j).symm, by simp [hmapφ]⟩
  have hfib : p.IsFibered := hp.isFibered
  refine ⟨V.I₀, y, φ, fun j => ?_, ?_, Vobj, vmap, hdom, hmapφ,
    B.ofArrows_inclusion_mem_fppfPrecoverage hV⟩
  · show IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y j)))
    rw [hdom j]
    exact hVaff j
  · refine (Functor.isInheritedTopology_inheritedTopology p
      (BigFppfOver.baseOverTopology B S hS .fppf) y φ hcart).2 ?_
    refine (BigFppfOver.baseOverTopology B S hS .fppf).superset_covering ?_ hBcover
    intro Z g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨j, a, rfl⟩ := hg
    exact (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)).downward_closed
      (hvmapmem j) a

/-- **Every object of the associated fppf site carries a covering family by affine objects.**
An affine open cover of the scheme underlying the image of the object is, after replacing it by a
combinatorial representative inside the chosen size-bounded category of schemes, one of the
site's covering families; lifting its members along `p` — possible because `p` is fibred in
groupoids, which also makes every lift strongly cartesian — produces a covering family for the
inherited topology whose members are affine. -/
theorem exists_affine_ofArrows (hp : p.IsFiberedInGroupoids) (W : 𝒳) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳) (φ : ∀ j, y j ⟶ W),
      (∀ j, IsAffineOver B S hS (p.obj (y j))) ∧
        Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS p .fppf W := by
  obtain ⟨I, y, φ, haff, hcov, -⟩ := exists_affine_ofArrows_aux B S hS p hp W
  exact ⟨I, y, φ, haff, hcov⟩

/-- **Every object of a slice of the associated fppf site carries a covering family by affine
objects.**  The family of `AlgebraicGeometry.FibredSite.exists_affine_ofArrows` at the underlying
object, each member equipped with the composite structure morphism. -/
theorem exists_affine_ofArrows_over (hp : p.IsFiberedInGroupoids) (x : 𝒳) (W : Over x) :
    ∃ (I : Type (u + 1)) (Y : I → Over x) (a : ∀ j, Y j ⟶ W),
      (∀ j, IsAffineOver B S hS (p.obj (Y j).left)) ∧
        Sieve.ofArrows Y a ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W := by
  obtain ⟨I, y, φ, hyaff, hcov⟩ := exists_affine_ofArrows B S hS p hp W.left
  refine ⟨I, fun j => Over.mk (φ j ≫ W.hom), fun j => Over.homMk (φ j), hyaff, ?_⟩
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact hcov

/-- The covering families of the associated fppf site all of whose members have affine source. -/
abbrev affinePrecoverage : Precoverage 𝒳 :=
  (BigFppfOver.associatedTopology B S hS p .fppf).precoverageOfObjects
    fun x => IsAffineOver B S hS (p.obj x)

/-- The covering families of a slice of the associated fppf site all of whose members have affine
source. -/
abbrev affinePrecoverageOver (x : 𝒳) : Precoverage (Over x) :=
  ((BigFppfOver.associatedTopology B S hS p .fppf).over x).precoverageOfObjects
    fun W => IsAffineOver B S hS (p.obj W.left)

/-- **The covering families by affine objects generate the inherited fppf topology.** -/
theorem generates_affinePrecoverage (hp : p.IsFiberedInGroupoids) :
    (affinePrecoverage B S hS p).Generates
      (BigFppfOver.associatedTopology B S hS p .fppf) :=
  GrothendieckTopology.generates_precoverageOfObjects _ _ (exists_affine_ofArrows B S hS p hp)

/-- **The covering families by affine objects generate the inherited fppf topology of a
slice.** -/
theorem generates_affinePrecoverageOver (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    (affinePrecoverageOver B S hS p x).Generates
      ((BigFppfOver.associatedTopology B S hS p .fppf).over x) :=
  GrothendieckTopology.generates_precoverageOfObjects _ _
    (exists_affine_ofArrows_over B S hS p hp x)

variable {A : Type*} [Category* A]

/-- **A presheaf on the associated fppf site which satisfies the sheaf condition for the covering
families by affine objects is a sheaf.** -/
theorem isSheaf_of_isSheafFor_affine (hp : p.IsFiberedInGroupoids) (F : 𝒳ᵒᵖ ⥤ A)
    (hF : ∀ ⦃W : 𝒳⦄ (R : Presieve W),
      Sieve.generate R ∈ BigFppfOver.associatedTopology B S hS p .fppf W →
      (∀ ⦃y : 𝒳⦄ (f : y ⟶ W), R f → IsAffineOver B S hS (p.obj y)) →
      ∀ M : A, Presieve.IsSheafFor (F ⋙ coyoneda.obj (op M)) R) :
    Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p .fppf) F :=
  (generates_affinePrecoverage B S hS p hp).isSheaf_iff.2 fun {_} R hR M => hF R hR.1 hR.2 M

/-- **A presheaf on a slice of the associated fppf site which satisfies the sheaf condition for
the covering families by affine objects is a sheaf.**  This is the criterion a module whose
sections are only computable over affine objects is proved to be a sheaf by. -/
theorem isSheaf_over_of_isSheafFor_affine (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (F : (Over x)ᵒᵖ ⥤ A)
    (hF : ∀ ⦃W : Over x⦄ (R : Presieve W),
      Sieve.generate R ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W →
      (∀ ⦃Y : Over x⦄ (f : Y ⟶ W), R f → IsAffineOver B S hS (p.obj Y.left)) →
      ∀ M : A, Presieve.IsSheafFor (F ⋙ coyoneda.obj (op M)) R) :
    Presheaf.IsSheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) F :=
  (generates_affinePrecoverageOver B S hS p hp x).isSheaf_iff.2
    fun {_} R hR M => hF R hR.1 hR.2 M

/-- **A presheaf on a slice of the associated fppf site which satisfies the sheaf condition for
the covering families of arrows with affine source is a sheaf.**  This is
`AlgebraicGeometry.FibredSite.isSheaf_over_of_isSheafFor_affine` with the covering presieve
presented as a family of arrows, which is the form in which the sheaf condition for a covering is
verified. -/
theorem isSheaf_over_of_isSheafFor_affine_ofArrows (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (F : (Over x)ᵒᵖ ⥤ A)
    (hF : ∀ (W : Over x) (I : Type (max v w)) (Y : I → Over x) (a : ∀ j, Y j ⟶ W),
      (∀ j, IsAffineOver B S hS (p.obj (Y j).left)) →
      Sieve.ofArrows Y a ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W →
      ∀ M : A, Presieve.IsSheafFor (F ⋙ coyoneda.obj (op M)) (Presieve.ofArrows Y a)) :
    Presheaf.IsSheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) F := by
  refine isSheaf_over_of_isSheafFor_affine B S hS p hp x F fun {W} R hR haff M => ?_
  obtain ⟨I, Y, a, rfl⟩ := R.exists_eq_ofArrows
  exact hF W I Y a (fun j => haff (a j) (Presieve.ofArrows.mk j)) hR M

/-- **A covering sieve of an affine object of a slice of the associated fppf site contains a
finite covering family of affine objects.**  An affine object has the finite subcovering property
(`AlgebraicGeometry.BigFppfOver.hasFiniteSubcovering_over_associatedTopology`), and the affine
objects cover every object, so
`CategoryTheory.GrothendieckTopology.exists_finite_ofArrows_le` applies. -/
theorem exists_finite_affine_ofArrows_le_over (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (f : y ⟶ x)
    (hy : IsAffineOver B S hS (p.obj y)) (S' : Sieve (Over.mk f))
    (hS' : S' ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) (Over.mk f)) :
    ∃ (n : ℕ) (Y : Fin n → Over x) (a : ∀ i, Y i ⟶ Over.mk f),
      (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) ∧ (∀ i, S' (a i)) ∧
        Sieve.ofArrows Y a ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
          (Over.mk f) :=
  GrothendieckTopology.exists_finite_ofArrows_le _
    (fun W : Over x => IsAffineOver B S hS (p.obj W.left))
    (exists_affine_ofArrows_over B S hS p hp x)
    (BigFppfOver.hasFiniteSubcovering_over_associatedTopology B S hS p hp f hy) S' hS'

end AlgebraicGeometry.FibredSite

/-! ### Recording the fppf condition of a refinement

The covering families by affine objects which refine a covering sieve are produced from affine
open covers, and the covering sieves they live in are generated by the fppf covering families of
the big site; both are fppf at the level of schemes.  The statements above do not record it,
because the sheaf-condition arguments which consume them do not look at the morphisms.  Descent
does: the ring map a covering morphism induces on global functions is faithfully flat precisely
because the morphism is flat and the family is jointly surjective.  The statements below are the
same refinements with the fppf condition of the refined family recorded. -/

namespace AlgebraicGeometry.Scheme

/-- **Membership in the fppf precoverage transports along isomorphisms of the sources.**  The
range of a morphism is unchanged by precomposing an isomorphism, and flatness and local finite
presentation are preserved by it.

This is what carries the fppf condition of a family of morphisms of schemes across the equality
of objects which a lift along a functor fibred in groupoids comes with. -/
theorem mem_fppfPrecoverage_of_forall_eq_comp {T : Scheme.{u}} {I : Type w'}
    {X X' : I → Scheme.{u}} {g : ∀ i, X i ⟶ T} {g' : ∀ i, X' i ⟶ T} (e : ∀ i, X' i ≅ X i)
    (he : ∀ i, g' i = (e i).hom ≫ g i)
    (hg : Presieve.ofArrows X g ∈ Scheme.fppfPrecoverage T) :
    Presieve.ofArrows X' g' ∈ Scheme.fppfPrecoverage T := by
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hg ⊢
  refine ⟨fun z => ?_, fun i => ?_⟩
  · obtain ⟨i, hi⟩ := hg.1 z
    exact ⟨i, (mem_range_iff_of_surjective (g' i) (g i) (e i).hom (he i).symm z).2 hi⟩
  · have h1 := (hg.2 i).1
    have h2 := (hg.2 i).2
    rw [he i]
    exact ⟨inferInstance, inferInstance⟩

/-- **Membership in the fppf precoverage transports along a reindexing of the family.**  Composing
the index with an equivalence changes neither the set of morphisms of the family nor the union of
their ranges. -/
theorem mem_fppfPrecoverage_of_equiv {T : Scheme.{u}} {I : Type w} {J : Type w'} (e : J ≃ I)
    {X : I → Scheme.{u}} {g : ∀ i, X i ⟶ T}
    (hg : Presieve.ofArrows X g ∈ Scheme.fppfPrecoverage T) :
    Presieve.ofArrows (fun j => X (e j)) (fun j => g (e j)) ∈ Scheme.fppfPrecoverage T := by
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hg ⊢
  refine ⟨fun z => ?_, fun j => hg.2 (e j)⟩
  obtain ⟨i, hi⟩ := hg.1 z
  exact ⟨e.symm i, by rwa [e.apply_symm_apply]⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.BigFppfSite

/-- **A covering sieve of a big fppf site contains a family whose image in schemes is an fppf
covering family.**  A covering sieve contains a selected covering family
(`AlgebraicGeometry.BigFppfSite.exists_isCovering_sieve₀_le`), and a selected covering family is
by definition one whose image in schemes is fppf. -/
theorem exists_fppf_ofArrows_le (B : BigFppfSite.{u}) {T : B.Schemes} {Sv : Sieve T}
    (hSv : Sv ∈ B.topology T) :
    ∃ (I : Type (u + 1)) (X : I → B.Schemes) (g : ∀ i, X i ⟶ T), (∀ i, Sv (g i)) ∧
      Presieve.ofArrows (fun i => B.inclusion.obj (X i)) (fun i => B.inclusion.map (g i)) ∈
        Scheme.fppfPrecoverage (B.inclusion.obj T) := by
  obtain ⟨E, hE, hES⟩ := B.exists_isCovering_sieve₀_le hSv
  exact ⟨E.I₀, E.X, E.f, fun i => hES _ (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i)),
    B.ofArrows_inclusion_mem_fppfPrecoverage hE⟩

end AlgebraicGeometry.BigFppfSite

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A covering sieve of the big fppf category over a scheme contains a family whose image in
schemes is an fppf covering family.**  The correspondence between sieves of a slice and sieves of
the underlying object (`CategoryTheory.GrothendieckTopology.mem_over_iff` and
`CategoryTheory.Sieve.overEquiv_iff`) reduces this to
`AlgebraicGeometry.BigFppfSite.exists_fppf_ofArrows_le`, the image in schemes of a morphism of the
slice being the image of its left component. -/
theorem exists_fppf_ofArrows_le_baseOverTopology {T : BigFppfOver B S hS} {Sv : Sieve T}
    (hSv : Sv ∈ baseOverTopology B S hS .fppf T) :
    ∃ (I : Type (u + 1)) (X : I → BigFppfOver B S hS) (g : ∀ i, X i ⟶ T), (∀ i, Sv (g i)) ∧
      Presieve.ofArrows (fun i => (toScheme B S hS).obj (X i))
          (fun i => (toScheme B S hS).map (g i)) ∈
        Scheme.fppfPrecoverage ((toScheme B S hS).obj T) := by
  change Sv ∈ (B.topology.over (B.obj hS)) T at hSv
  rw [GrothendieckTopology.mem_over_iff] at hSv
  obtain ⟨I, X, g, hmem, hfppf⟩ := B.exists_fppf_ofArrows_le hSv
  refine ⟨I, fun i => Over.mk (g i ≫ T.hom), fun i => Over.homMk (g i),
    fun i => (Sieve.overEquiv_iff Sv (g i)).1 (hmem i), hfppf⟩

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **A covering sieve of the associated fppf site contains a family whose image in schemes is an
fppf covering family.**  A covering sieve of the inherited topology contains an inherited covering
family, whose images generate a covering sieve downstairs; that sieve contains a family which is
fppf in schemes (`AlgebraicGeometry.BigFppfOver.exists_fppf_ofArrows_le_baseOverTopology`), each
of whose members factors through the image of a member of the first family; and each of those
factorizations lifts along the structure functor, the fibred category being fibred in groupoids,
to a morphism of the fibred category which lies in the sieve and whose image agrees with the fppf
morphism up to the isomorphism of sources the lift comes with. -/
theorem exists_fppf_ofArrows_le (hp : p.IsFiberedInGroupoids) {x : 𝒳} {Sv : Sieve x}
    (hSv : Sv ∈ BigFppfOver.associatedTopology B S hS p .fppf x) :
    ∃ (I : Type (u + 1)) (z : I → 𝒳) (φ : ∀ i, z i ⟶ x), (∀ i, Sv (φ i)) ∧
      Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (p.obj (z i)))
          (fun i => (BigFppfOver.toScheme B S hS).map (p.map (φ i))) ∈
        Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj x)) := by
  have hfib : p.IsFibered := hp.isFibered
  rw [BigFppfOver.associatedTopology, Functor.inheritedTopology,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hSv
  obtain ⟨R, hR, hRS⟩ := hSv
  have hbase : Sieve.generate (R.map p) ∈
    BigFppfOver.baseOverTopology B S hS .fppf (p.obj x) := hR.2
  obtain ⟨I, Xb, gb, hmem, hfppf⟩ :=
    BigFppfOver.exists_fppf_ofArrows_le_baseOverTopology B S hS hbase
  have hex : ∀ i, ∃ (wi : 𝒳) (fi : wi ⟶ x) (ci : Xb i ⟶ p.obj wi),
      R fi ∧ ci ≫ p.map fi = gb i := by
    intro i
    obtain ⟨Z, a, b, hb, hfac⟩ := hmem i
    obtain ⟨hu⟩ := hb
    exact ⟨_, _, a, hu, hfac⟩
  choose wo fo co hRfo hfaco using hex
  choose zo ψ hdom hψ using fun i => exists_lift_map_eq_eqToHom_comp B S hS p hp (co i)
  have hmapφ : ∀ i, p.map (ψ i ≫ fo i) = eqToHom (hdom i) ≫ gb i := fun i => by
    rw [p.map_comp, hψ, Category.assoc, hfaco]
  refine ⟨I, zo, fun i => ψ i ≫ fo i,
    fun i => Sv.downward_closed (hRS _ _ (hRfo i)) _, ?_⟩
  refine Scheme.mem_fppfPrecoverage_of_forall_eq_comp
    (fun i => eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj (hdom i))) (fun i => ?_) hfppf
  rw [hmapφ i, Functor.map_comp, eqToIso.hom, eqToHom_map]

/-- **Every object of the associated fppf site carries a covering family by affine objects whose
image in schemes is an fppf covering family.**  This is
`AlgebraicGeometry.FibredSite.exists_affine_ofArrows` with the fppf condition of the family
recorded: the affine open cover the family is built from is replaced by a selected covering family
of the big site, which is fppf in schemes by definition, and lifting along a functor fibred in
groupoids changes the family only by the isomorphism of sources the lift comes with. -/
theorem exists_affine_fppf_ofArrows (hp : p.IsFiberedInGroupoids) (W : 𝒳) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳) (φ : ∀ j, y j ⟶ W),
      (∀ j, IsAffineOver B S hS (p.obj (y j))) ∧
        Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS p .fppf W ∧
        Presieve.ofArrows (fun j => (BigFppfOver.toScheme B S hS).obj (p.obj (y j)))
            (fun j => (BigFppfOver.toScheme B S hS).map (p.map (φ j))) ∈
          Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj W)) := by
  obtain ⟨I, y, φ, haff, hcov, X, g, hdom, hmapφ, hfppf⟩ :=
    exists_affine_ofArrows_aux B S hS p hp W
  refine ⟨I, y, φ, haff, hcov, Scheme.mem_fppfPrecoverage_of_forall_eq_comp
    (fun j => eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj (hdom j)))
    (fun j => ?_) hfppf⟩
  rw [hmapφ j, Functor.map_comp, eqToIso.hom, eqToHom_map]

/-- **A covering sieve of an affine object of the associated fppf site contains a finite family of
affine objects whose image in schemes is an fppf covering family.**

The sieve contains a family which is fppf in schemes
(`AlgebraicGeometry.FibredSite.exists_fppf_ofArrows_le`); refining each of its members by a
covering family of affine objects which is again fppf
(`AlgebraicGeometry.FibredSite.exists_affine_fppf_ofArrows`) keeps the composite family inside the
sieve, makes every source affine, and keeps it fppf because the fppf precoverage of schemes is
stable under composition; and the underlying scheme of an affine object is quasi-compact, so
finitely many members of the composite family already cover
(`AlgebraicGeometry.Scheme.exists_finset_ofArrows_mem_fppfPrecoverage`). -/
theorem exists_finite_affine_fppf_ofArrows_le (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    (hx : IsAffineOver B S hS (p.obj x)) {Sv : Sieve x}
    (hSv : Sv ∈ BigFppfOver.associatedTopology B S hS p .fppf x) :
    ∃ (n : ℕ) (z : Fin n → 𝒳) (φ : ∀ i, z i ⟶ x),
      (∀ i, IsAffineOver B S hS (p.obj (z i))) ∧ (∀ i, Sv (φ i)) ∧
        Sieve.ofArrows z φ ∈ BigFppfOver.associatedTopology B S hS p .fppf x ∧
        Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (p.obj (z i)))
            (fun i => (BigFppfOver.toScheme B S hS).map (p.map (φ i))) ∈
          Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj x)) := by
  classical
  obtain ⟨I, zb, φb, hmemb, hfppfb⟩ := exists_fppf_ofArrows_le B S hS p hp hSv
  choose Ji yi ψi haffi hcovi hfppfi using
    fun i => exists_affine_fppf_ofArrows B S hS p hp (zb i)
  have hcomp : Presieve.ofArrows
      (fun k : Σ i, Ji i => (BigFppfOver.toScheme B S hS).obj (p.obj (yi k.1 k.2)))
      (fun k : Σ i, Ji i =>
        (BigFppfOver.toScheme B S hS).map (p.map (ψi k.1 k.2 ≫ φb k.1))) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj x)) := by
    have h := Precoverage.comp_mem_coverings
      (J := Scheme.fppfPrecoverage) (fun i => (BigFppfOver.toScheme B S hS).map (p.map (φb i)))
      hfppfb (fun i j => (BigFppfOver.toScheme B S hS).map (p.map (ψi i j))) hfppfi
    simpa only [p.map_comp, Functor.map_comp] using h
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj (p.obj x)) :=
    B.compactSpace_of_isAffine (p.obj x).left hx
  obtain ⟨s, hs⟩ := Scheme.exists_finset_ofArrows_mem_fppfPrecoverage hcomp
  refine ⟨s.card, fun i => yi (s.equivFin.symm i).1.1 (s.equivFin.symm i).1.2,
    fun i => ψi (s.equivFin.symm i).1.1 (s.equivFin.symm i).1.2 ≫ φb (s.equivFin.symm i).1.1,
    fun i => haffi _ _, fun i => Sv.downward_closed (hmemb _) _, ?_, ?_⟩
  · exact ofArrows_mem_associatedTopology B S hS p hp _ _
      (BigFppfOver.ofArrows_mem_baseOverTopology B S hS _ _
        (Scheme.mem_fppfPrecoverage_of_equiv s.equivFin.symm hs))
  · exact Scheme.mem_fppfPrecoverage_of_equiv s.equivFin.symm hs

/-- **A covering sieve of an affine object of a slice of the associated fppf site contains a
finite family of affine objects whose image in schemes is an fppf covering family.**  This is
`AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le` transported to the slice by
the correspondence between covering sieves of `CategoryTheory.Over.mk f` and covering sieves of
its underlying object, which changes neither the underlying schemes nor the morphisms between
them.

It is `AlgebraicGeometry.FibredSite.exists_finite_affine_ofArrows_le_over` with the fppf condition
of the refined family recorded, and that condition is what descent needs: the ring map a member of
the family induces on global functions is faithfully flat, because the member is flat and the
family is jointly surjective, so the Amitsur complex of that ring map computes the sections over
the affine object. -/
theorem exists_finite_affine_fppf_ofArrows_le_over (hp : p.IsFiberedInGroupoids) {x y : 𝒳}
    (f : y ⟶ x) (hy : IsAffineOver B S hS (p.obj y)) (S' : Sieve (Over.mk f))
    (hS' : S' ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) (Over.mk f)) :
    ∃ (n : ℕ) (Y : Fin n → Over x) (a : ∀ i, Y i ⟶ Over.mk f),
      (∀ i, IsAffineOver B S hS (p.obj (Y i).left)) ∧ (∀ i, S' (a i)) ∧
        Sieve.ofArrows Y a ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
          (Over.mk f) ∧
        Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left))
            (fun i => (BigFppfOver.toScheme B S hS).map (p.map (a i).left)) ∈
          Scheme.fppfPrecoverage
            ((BigFppfOver.toScheme B S hS).obj (p.obj (Over.mk f).left)) := by
  rw [GrothendieckTopology.mem_over_iff] at hS'
  obtain ⟨n, z, φ, haff, hmem, hcov, hfppf⟩ :=
    exists_finite_affine_fppf_ofArrows_le B S hS p hp hy hS'
  refine ⟨n, fun i => Over.mk (φ i ≫ f), fun i => Over.homMk (φ i), haff,
    fun i => (Sieve.overEquiv_iff S' (φ i)).1 (hmem i), ?_, hfppf⟩
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact hcov

end AlgebraicGeometry.FibredSite

end
