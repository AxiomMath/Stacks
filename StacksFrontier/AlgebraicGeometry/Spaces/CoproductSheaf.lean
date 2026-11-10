module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluing

/-!
# A coproduct of schemes in the big fppf site is a coproduct of representable sheaves

This is the direction opposite to Stacks 02WO. If an object `V` of the big fppf site over `S`
is the coproduct *in schemes* of a family of objects `U i` of that site, then the sheaf
represented by `V` is the coproduct of the sheaves represented by the `U i`. Together with the
0F15 representability of the resulting inclusions this is the geometric input of Stacks 02WQ,
the algebraicity of a coproduct of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.sigmaOver` and
  `AlgebraicGeometry.BigFppfOver.sigmaOverInj` are the coproduct of a family of objects of the
  big fppf site over `S` whose underlying schemes have a coproduct satisfying the site's size
  bound, together with its inclusions.
* `AlgebraicGeometry.Space.isColimit_yoneda_of_isColimit_toScheme` is the colimit cofan of
  sheaves produced by a colimit cofan of schemes.

## Main results

* `AlgebraicGeometry.isOpenImmersion_of_isColimit_cofanMk`,
  `AlgebraicGeometry.exists_mem_range_of_isColimit_cofanMk` and
  `AlgebraicGeometry.isEmpty_of_commSq_of_isColimit_cofanMk` read off a colimit cofan of
  schemes that its legs are open immersions, that they are jointly surjective, and that two
  distinct legs have no common point.
* `AlgebraicGeometry.BigFppfOver.sieve_ofArrows_mem_topology_of_isColimit`: the legs of a cofan
  in the big fppf site over `S` whose underlying cofan of schemes is a colimit generate a
  covering sieve.
* `AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof` (from
  `StacksFrontier.AlgebraicGeometry.Spaces.CoproductCutoff`) and
  `AlgebraicGeometry.BigFppfOver.isColimit_toScheme_sigmaOver` show the hypothesis of
  `AlgebraicGeometry.Space.isColimit_yoneda_of_isColimit_toScheme` is satisfied by every at
  most countable family of objects of the site, so in particular by families of two or more
  genuinely distinct summands.

## Implementation notes

The index type is required to be `Small.{u}`. This is forced from two sides: a coproduct of
`AlgebraicGeometry.Scheme.{u}` indexed outside `Type u` need not exist, while the covering
families of a big fppf site are indexed in `Type (u + 1)`; a `Small.{u}` index type meets both
demands, since `Small.{u}` implies `Small.{u + 1}`. The hypothesis cannot be dropped by
appealing to the given colimit: a cofan of empty schemes with empty vertex is a colimit cofan
for an index type of any size.

The three scheme-level facts are read off the canonical isomorphism between the vertex of the
given cofan and Mathlib's chosen coproduct `∐ X`, whose coproduct inclusions are open
immersions, are jointly surjective by `AlgebraicGeometry.sigmaOpenCover`, and are pairwise
disjoint by `AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne`.

Passing from the scheme-level colimit to the sheaf-level one is
`CategoryTheory.GrothendieckTopology.isColimitCofanMkYoneda`, whose three inputs are the
covering sieve, `AlgebraicGeometry.BigFppfOver.bot_mem_topology_of_isInitial`, and
disjointness transported through the faithful functor to schemes. The covering sieve is
obtained by reindexing the family along `CategoryTheory.PreZeroHypercover.reindex`, which
leaves the generated presieve unchanged, and then by
`AlgebraicGeometry.BigFppfSite.generate_mem_topology`, which does not require the family to be
one of the site's chosen ones.

## References

* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe v u

namespace AlgebraicGeometry

/-! ### Colimit cofans of schemes -/

section Schemes

variable {I : Type v} [Small.{u} I] {X : I → Scheme.{u}} {Y : Scheme.{u}}
  {f : ∀ i, X i ⟶ Y}

/-- A leg of a colimit cofan of schemes agrees, after the canonical isomorphism of its vertex
with the chosen coproduct, with the corresponding coproduct inclusion. -/
theorem comp_isColimit_cofanMk_iso_hom (hc : IsColimit (Cofan.mk Y f)) (i : I) :
    f i ≫ (hc.coconePointUniqueUpToIso (coproductIsCoproduct X)).hom = Sigma.ι X i := by
  simpa using hc.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct X) ⟨i⟩

/-- Every leg of a colimit cofan of schemes is an open immersion. -/
theorem isOpenImmersion_of_isColimit_cofanMk (hc : IsColimit (Cofan.mk Y f)) (i : I) :
    IsOpenImmersion (f i) := by
  have h : IsOpenImmersion
      (f i ≫ (hc.coconePointUniqueUpToIso (coproductIsCoproduct X)).hom) := by
    rw [comp_isColimit_cofanMk_iso_hom hc i]
    infer_instance
  exact (MorphismProperty.cancel_right_of_respectsIso
    (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) (f i) _).1 h

/-- The legs of a colimit cofan of schemes are jointly surjective. -/
theorem exists_mem_range_of_isColimit_cofanMk (hc : IsColimit (Cofan.mk Y f)) (y : Y) :
    ∃ i, y ∈ Set.range (f i) := by
  let e := hc.coconePointUniqueUpToIso (coproductIsCoproduct X)
  have hinj : Function.Injective e.hom.base := fun a b h => by
    simpa [← Scheme.Hom.comp_apply] using congrArg e.inv.base h
  obtain ⟨z, hz⟩ := (sigmaOpenCover X).covers (e.hom.base y)
  let k : I := (sigmaOpenCover X).idx (e.hom.base y)
  refine ⟨k, show X k from z, hinj ?_⟩
  rwa [← Scheme.Hom.comp_apply, comp_isColimit_cofanMk_iso_hom hc k]

/-- Two distinct legs of a colimit cofan of schemes have no common point: a scheme mapping to
both of their sources so that the resulting square commutes is empty. -/
theorem isEmpty_of_commSq_of_isColimit_cofanMk (hc : IsColimit (Cofan.mk Y f))
    {i i' : I} (hii' : i ≠ i') {Z : Scheme.{u}} {a : Z ⟶ X i} {b : Z ⟶ X i'}
    (hab : a ≫ f i = b ≫ f i') : IsEmpty Z := by
  refine isEmpty_of_commSq_sigmaι_of_ne (a := a) (b := b) ⟨?_⟩ hii'
  rw [← comp_isColimit_cofanMk_iso_hom hc i, ← comp_isColimit_cofanMk_iso_hom hc i',
    ← Category.assoc, ← Category.assoc, hab]

end Schemes

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The covering sieve generated by a scheme-level coproduct decomposition -/

private theorem cofanHypercover_isFppf {I : Type v} [Small.{u} I]
    (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ i, U i ⟶ V)
    (hV : IsColimit (Cofan.mk ((toScheme B S hS).obj V)
      (fun i => (toScheme B S hS).map (j i)))) :
    IsFppfCovering ⟨V.left,
      (coverHypercover B S hS U V j).map (Over.forget (B.obj hS))⟩ := by
  have hZ : (Presieve.ofArrows (fun i => (toScheme B S hS).obj (U i))
      (fun i => (toScheme B S hS).map (j i))) ∈
      Scheme.zariskiPrecoverage ((toScheme B S hS).obj V) :=
    (Scheme.ofArrows_mem_precoverage_iff
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})).2
      ⟨exists_mem_range_of_isColimit_cofanMk hV, isOpenImmersion_of_isColimit_cofanMk hV⟩
  unfold IsFppfCovering
  rw [Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_map,
    presieve₀_coverHypercover, Presieve.map_ofArrows, Presieve.map_ofArrows]
  exact Scheme.zariskiPrecoverage_le_fppfPrecoverage ((toScheme B S hS).obj V) hZ

/-- The legs of a cofan in the big fppf site over `S` whose underlying cofan of schemes is a
colimit generate a covering sieve. The family need not be one of the site's chosen covering
families: it is a Zariski, hence fppf, covering because its legs are jointly surjective open
immersions. -/
theorem sieve_ofArrows_mem_topology_of_isColimit {I : Type v} [Small.{u} I]
    (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ i, U i ⟶ V)
    (hV : IsColimit (Cofan.mk ((toScheme B S hS).obj V)
      (fun i => (toScheme B S hS).map (j i)))) :
    Sieve.ofArrows U j ∈ topology B S hS V := by
  have hgen := B.generate_mem_topology
    ((coverHypercover B S hS U V j).map (Over.forget (B.obj hS)))
    (cofanHypercover_isFppf B S hS U V j hV)
  have heq : Sieve.ofArrows U j =
      (Sieve.overEquiv V).symm
        (Sieve.ofArrows (fun i => (U i).left) (fun i => (j i).left)) :=
    (Sieve.overEquiv V).eq_symm_apply.2 (Sieve.overEquiv_ofArrows (X := B.obj hS) (Y := V) _ _)
  rw [heq]
  apply B.topology.overEquiv_symm_mem_over
  rwa [PreZeroHypercover.presieve₀_map, presieve₀_coverHypercover,
    Presieve.map_ofArrows] at hgen

/-! ### Coproducts of objects of the site -/

/-- The coproduct of a family of objects of the big fppf site over `S`, under the assumption
that the coproduct of their underlying schemes satisfies the site's size bound. -/
noncomputable def sigmaOver {I : Type v} [Small.{u} I] (U : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (toScheme B S hS).obj (U i))) : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (X := B.obj hsum) (Y := B.obj hS)
    (Sigma.desc fun i => B.inclusion.map (U i).hom))

/-- The inclusion of a summand into `AlgebraicGeometry.BigFppfOver.sigmaOver`. -/
noncomputable def sigmaOverInj {I : Type v} [Small.{u} I] (U : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (toScheme B S hS).obj (U i))) (i : I) :
    U i ⟶ sigmaOver B S hS U hsum :=
  Over.homMk (B.inclusion.preimage (X := (U i).left) (Y := B.obj hsum)
    (Sigma.ι (fun k => (toScheme B S hS).obj (U k)) i)) (by
      apply B.inclusion.map_injective
      change B.inclusion.map (B.inclusion.preimage (X := (U i).left) (Y := B.obj hsum)
          (Sigma.ι (fun k => (toScheme B S hS).obj (U k)) i) ≫
        B.inclusion.preimage (X := B.obj hsum) (Y := B.obj hS)
          (Sigma.desc fun k => B.inclusion.map (U k).hom)) =
        B.inclusion.map (U i).hom
      rw [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
      exact Sigma.ι_comp_desc _ i)

/-- The underlying scheme morphism of `AlgebraicGeometry.BigFppfOver.sigmaOverInj` is the
coproduct inclusion. -/
theorem toScheme_map_sigmaOverInj {I : Type v} [Small.{u} I] (U : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (toScheme B S hS).obj (U i))) (i : I) :
    (toScheme B S hS).map (sigmaOverInj B S hS U hsum i) =
      Sigma.ι (fun k => (toScheme B S hS).obj (U k)) i :=
  B.inclusion.map_preimage _

/-- The cofan of `AlgebraicGeometry.BigFppfOver.sigmaOverInj` is a colimit after passing to
underlying schemes. -/
noncomputable def isColimit_toScheme_sigmaOver {I : Type v} [Small.{u} I]
    (U : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (toScheme B S hS).obj (U i))) :
    IsColimit (Cofan.mk ((toScheme B S hS).obj (sigmaOver B S hS U hsum))
      (fun i => (toScheme B S hS).map (sigmaOverInj B S hS U hsum i))) := by
  have h : (fun i => (toScheme B S hS).map (sigmaOverInj B S hS U hsum i)) =
      Sigma.ι (fun k => (toScheme B S hS).obj (U k)) :=
    funext fun i => toScheme_map_sigmaOverInj B S hS U hsum i
  rw [h]
  exact coproductIsCoproduct _

end BigFppfOver

namespace Space

open AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A leg of a cofan in the big fppf site over `S` whose underlying cofan of schemes is a
colimit is a monomorphism. -/
theorem mono_of_isColimit_toScheme {I : Type v} [Small.{u} I]
    (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ i, U i ⟶ V)
    (hV : IsColimit (Cofan.mk ((toScheme B S hS).obj V)
      (fun i => (toScheme B S hS).map (j i)))) (i : I) : Mono (j i) := by
  apply (Over.forget (B.obj hS)).mono_of_mono_map
  apply B.inclusion.mono_of_mono_map
  have := isOpenImmersion_of_isColimit_cofanMk hV i
  exact _root_.AlgebraicGeometry.IsOpenImmersion.mono ((toScheme B S hS).map (j i))

/-- **The representable sheaf of a scheme coproduct is the sheaf coproduct.** If an object `V`
of the big fppf site over `S` is, in schemes, the coproduct of the objects `U i`, then the
sheaf represented by `V` is the coproduct of the sheaves represented by the `U i`. This is the
direction opposite to Stacks 02WO. -/
noncomputable def isColimit_yoneda_of_isColimit_toScheme
    [(topology B S hS).Subcanonical] {I : Type v} [Small.{u} I]
    (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ i, U i ⟶ V)
    (hV : IsColimit (Cofan.mk ((toScheme B S hS).obj V)
      (fun i => (toScheme B S hS).map (j i)))) :
    IsColimit (Cofan.mk ((topology B S hS).yoneda.obj V)
      (fun i => (topology B S hS).yoneda.map (j i))) := by
  have : ∀ i, Mono ((Cofan.mk V j).inj i) := fun i =>
    mono_of_isColimit_toScheme B S hS U V j hV i
  refine (topology B S hS).isColimitCofanMkYoneda U (c := Cofan.mk V j) ?_
    (BigFppfOver.bot_mem_topology_of_isInitial B S hS) ?_
  · simpa using sieve_ofArrows_mem_topology_of_isColimit B S hS U V j hV
  · intro i i' hii' Y a b hab
    have hab' : (toScheme B S hS).map a ≫ (toScheme B S hS).map (j i) =
        (toScheme B S hS).map b ≫ (toScheme B S hS).map (j i') := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (toScheme B S hS).map (by simpa using hab)
    exact ⟨Over.isInitialOfIsInitialLeft (Y := Y) (isInitial_schemeBelow B
      (isInitial_iff_isEmpty.mpr (isEmpty_of_commSq_of_isColimit_cofanMk hV hii' hab')).some)⟩

/-- The hypothesis of `AlgebraicGeometry.Space.isColimit_yoneda_of_isColimit_toScheme` is
satisfied by every at most countable family of objects of the big fppf site over `S`: the
coproduct of their underlying schemes again satisfies the site's size bound, so the sheaves
they represent have a representable coproduct. -/
noncomputable def isColimit_yoneda_sigmaOver_of_countable
    [(topology B S hS).Subcanonical] {I : Type u} (hI : #I ≤ ℵ₀)
    (U : I → BigFppfOver B S hS) :
    IsColimit (Cofan.mk ((topology B S hS).yoneda.obj (sigmaOver B S hS U
        (B.contains_sigma_of_lt_cof (lt_of_le_of_lt hI B.aleph0_lt_cutoff_cof) _
          fun i => (U i).left.2)))
      (fun i => (topology B S hS).yoneda.map (sigmaOverInj B S hS U
        (B.contains_sigma_of_lt_cof (lt_of_le_of_lt hI B.aleph0_lt_cutoff_cof) _
          fun i => (U i).left.2) i))) :=
  isColimit_yoneda_of_isColimit_toScheme B S hS U _ _
    (isColimit_toScheme_sigmaOver B S hS U _)

end Space

end AlgebraicGeometry

end
