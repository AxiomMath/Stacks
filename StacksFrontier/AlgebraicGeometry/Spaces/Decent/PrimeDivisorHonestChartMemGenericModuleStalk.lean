module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapFinitePresentationClause
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkClosedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericModuleStalkMem
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints

/-!
# An honest section on a chart through `ξ` puts a meromorphic section in `ℒ_ξ`

Let `X` be a decent algebraic space over `S`, let `Z ⊆ X` be a prime divisor with generic point
`ξ`, let `ℒ` be an *invertible* `𝒪_X`-module and let `s` be a meromorphic section of `ℒ`. If `s`
is an honest section of `ℒ` over **one** étale chart `W` of `X` whose image on points contains
`ξ`, then `s` lies in `ℒ_ξ`.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_subset_of_isOpen_of_forall_eq_top`: a morphism out of
  a represented presheaf whose chosen point lies in no proper open of the representing scheme has
  its image on points inside every open subset of the target containing the image of that point.
* `AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_eval_eq_of_mem_range`: a
  meromorphic section of an invertible module which is an honest section over an étale chart whose
  image contains `ξ` satisfies `AlgebraicGeometry.Space.PrimeDivisor.MemGenericModuleStalk`.

## References

* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism out of the spectrum of a local ring has its image inside every open containing
the image of the closed point.** Let `A` be an object of the big fppf site of `S` and let `a` be
a point of the presheaf it represents which lies in no proper open of the representing scheme —
the closed point of the spectrum of a local ring is such a point. Then the image on points of
any morphism out of `h_A` lies inside every open subset of the target containing the image
of `a`. -/
theorem range_pointsMap_subset_of_isOpen_of_forall_eq_top {A : BigFppfOver B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : yoneda.obj A ⟶ Y)
    (a : points B S hS (yoneda.obj A))
    (htop : ∀ V : ((BigFppfOver.toScheme B S hS).obj A).Opens,
      pointsToScheme B S hS A a ∈ V → V = ⊤)
    (U : Set (points B S hS Y)) (hUopen : IsOpen U)
    (hmem : pointsMap B S hS (yoneda.obj A) f a ∈ U) :
    Set.range (pointsMap B S hS (yoneda.obj A) f) ⊆ U := by
  have hpre : IsOpen (pointsMap B S hS (yoneda.obj A) f ⁻¹' U) :=
    hUopen.preimage (continuous_pointsMap B S hS f)
  set V : ((BigFppfOver.toScheme B S hS).obj A).Opens :=
    ⟨schemePointsHomeomorph B S hS A '' (pointsMap B S hS (yoneda.obj A) f ⁻¹' U),
      (schemePointsHomeomorph B S hS A).isOpen_image.2 hpre⟩
  have haV : pointsToScheme B S hS A a ∈ V := ⟨a, hmem, rfl⟩
  rintro - ⟨z, rfl⟩
  have hzV : pointsToScheme B S hS A z ∈ V := by
    rw [htop V haV]
    trivial
  obtain ⟨z', hz', hz'eq⟩ := hzV
  exact (schemePointsHomeomorph B S hS A).injective hz'eq ▸ hz'

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (R : Type u) [CommRing R] [IsLocalRing R]
    [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point) R]
    [IsLocalRing.IsHenselization
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)
      (IsLocalRing.ResidueField
        ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
          (Z.genericChart B S hS hX hdec).point)) R]
    (hR : B.Contains (Spec (.of R)))

/-- **The image of `c_ξ` on points lies inside every open subset of `|X|` containing `ξ`.** -/
theorem PrimeDivisor.range_pointsMap_genericHenselianMorphism_subset
    (U : Set (points B S hS X)) (hUopen : IsOpen U)
    (hmem : Z.genericPoint B S hS X ∈ U) :
    Set.range (pointsMap B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianMorphism B S hS hX hdec R hR).hom) ⊆ U := by
  refine range_pointsMap_subset_of_isOpen_of_forall_eq_top B S hS
    (Z.genericHenselianMorphism B S hS hX hdec R hR).hom
    (Z.genericHenselianClosedPoint B S hS hX hdec R hR) (fun V hV => ?_) U hUopen ?_
  · exact AlgebraicGeometry.forall_eq_top_of_mem_of_isLocalRing (CommRingCat.of R) V
      (by rwa [← (Z.genericChart B S hS hX hdec).pointsToScheme_henselianClosedPoint R hR])
  · exact Set.mem_of_eq_of_mem
      (Z.pointsMap_genericHenselianMorphism_closedPoint B S hS hX hdec R hR) hmem

/-- **A meromorphic section of an invertible module which is an honest section over a chart whose
image contains `ξ` lies in `ℒ_ξ`.**

Let `ℒ` be an invertible `𝒪_X`-module, let `s` be a meromorphic section of `ℒ` and let `W` be an
étale chart of `X` over which `s` is the image of a section `e` of `ℒ` under
`AlgebraicGeometry.Space.toMeromorphicSectionValue`. If the generic point `ξ` of the prime
divisor `Z` lies in the image of `W` on points, then
`AlgebraicGeometry.Space.PrimeDivisor.MemGenericModuleStalk` holds: the germ of `s` at `ξ` is the
image of a section of `ℒ_ξ`. -/
theorem PrimeDivisor.memGenericModuleStalk_of_eval_eq_of_mem_range
    (L : Modules.{u, u} B S hS X hX)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (W : SmallEtale B S hS X)
    (e : L.val.obj (op W))
    (he : s.eval (op W) = toMeromorphicSectionValue B S hS X hX L W e)
    (hmem : Z.genericPoint B S hS X ∈
      Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X).obj W)) W.1.hom)) :
    Z.MemGenericModuleStalk B S hS hX hdec R hR L s := by
  set P : SmallEtale B S hS X → Prop := fun V =>
    ∃ e' : L.val.obj (op V), s.eval (op V) = toMeromorphicSectionValue B S hS X hX L V e'
  have hPhom : ∀ {V V' : SmallEtale B S hS X}, (V' ⟶ V) → P V → P V' := fun φ ⟨e', he'⟩ =>
    ⟨(L.val.map φ.op).hom e', eval_eq_toMeromorphicSectionValue_of_hom B S hS X hX L s φ e' he'⟩
  have hPcov : ∀ x : points B S hS X,
      x ∈ Set.range (pointsMap B S hS
          (Z.genericHenselianSpace B S hS hX hdec R hR).obj
          (Z.genericHenselianMorphism B S hS hX hdec R hR).hom) →
        ∃ V : SmallEtale B S hS X, P V ∧
          x ∈ Set.range (pointsMap B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.1.hom) := fun x hx =>
    ⟨W, ⟨e, he⟩, Z.range_pointsMap_genericHenselianMorphism_subset B S hS hX hdec R hR _
      (isOpen_range_pointsMap_of_isEtale B S hS W.1.hom
        (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X).obj W)) hX
        ((isEtale_iff_presheaf_of_yoneda B S hS W.1.hom).mpr W.property)) hmem hx⟩
  refine Z.memGenericModuleStalk_of_sieve B S hS hX hdec R hR L hL s
    { arrows := fun W' _ => ∃ e' :
          (Z.genericHenselianPullback B S hS hX hdec R hR L).val.obj (op W'),
        (pullbackMeromorphicSection B S hS
              (Z.genericHenselianMorphism B S hS hX hdec R hR) L
              (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR)
              s).eval (op W') =
          toMeromorphicSectionValue B S hS
            (Z.genericHenselianSpace B S hS hX hdec R hR).obj
            (Z.genericHenselianSpace B S hS hX hdec R hR).property
            (Z.genericHenselianPullback B S hS hX hdec R hR L) W' e'
      downward_closed := by
        rintro W' W'' k ⟨e', he'⟩ c
        exact ⟨((Z.genericHenselianPullback B S hS hX hdec R hR L).val.map c.op).hom e',
          eval_eq_toMeromorphicSectionValue_of_hom B S hS
            (Z.genericHenselianSpace B S hS hX hdec R hR).obj
            (Z.genericHenselianSpace B S hS hX hdec R hR).property
            (Z.genericHenselianPullback B S hS hX hdec R hR L) _ c e' he'⟩ }
    ?_ (fun _ _ hk => hk)
  refine mem_topology_of_hasAffineChartDiagramWith_onRange B S hS P
    (Z.genericHenselianMorphism B S hS hX hdec R hR) hPhom hPcov _ _ ?_
  intro W' k hW'
  obtain ⟨-, V, q, hcomm, -, e', he'⟩ := hW'
  exact ⟨_, pullbackMeromorphicSection_eval_toMeromorphicSectionValue B S hS
    (Z.genericHenselianMorphism B S hS hX hdec R hR) L
    (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR) s
    ⟨W', V, q, hcomm.symm⟩ e' he'⟩

end AlgebraicGeometry.Space

end
