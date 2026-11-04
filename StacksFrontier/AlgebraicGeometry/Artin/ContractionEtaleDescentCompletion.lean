module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleDescentOpen

/-!
# Étale descent of a morphism out of a completion along a set of points

Let `{V_i ⟶ V}` be a family of objects of the big fppf site over `S` which generates a
covering sieve, let `Z` be a set of points of `V` and let `Z_i` be its inverse image in `V_i`.
This file proves that the family of completion subfunctors
`{V_{i,/Z_i} ⟶ V_{/Z}}` of Stacks 0AMC generates a covering sieve of sections of `V_{/Z}` at
every object of the site, so that a morphism from `V_{/Z}` into an fppf sheaf is glued from,
and determined by, its restrictions to the `V_{i,/Z_i}`.

That is the third of the four missing descent statements of Stacks 0GHG: the descent of the
third component `x̂ : V_{/Z} ⟶ W` of a section of Artin's contraction functor.

## Main results

* `AlgebraicGeometry.Space.familyImage_sieveOfSection_mem_completionSubfunctor`: **the missing
  statement.** The family of completions `{V_{i,/Z_i} ⟶ V_{/Z}}` generates a covering sieve of
  sections of `V_{/Z}`.
* `AlgebraicGeometry.Space.compatible_of_overlap_completionSubfunctor`: agreement of the two
  restrictions to the overlaps `V_i ×_V V_j` implies the compatibility hypothesis of
  `AlgebraicGeometry.Space.glueHom`, which quantifies over all objects of the site. This is
  where the fibre products of the covering family — Stacks 0GE1 part (3) for an étale covering
  of the locally Noetherian site — are needed.
* `AlgebraicGeometry.Space.glueHom_completionSubfunctor` and
  `AlgebraicGeometry.Space.hom_ext_completionSubfunctor`: a morphism from `V_{/Z}` into an fppf
  sheaf of `Type (u + 1)` is glued from, and determined by, its restrictions.

## What is and is not proved

Nothing is assumed; every declaration here is proved outright. Nothing carries a Stacks
attribute.

The statements are about the completion *subfunctor* of Stacks 0AMC rather than its fppf
sheafification `AlgebraicGeometry.Space.completionSheaf`. That is the sharper statement and
the one a proof uses: a morphism out of the sheafification into a sheaf is the same thing as a
morphism out of the subfunctor, by the universal property of sheafification, so the glueing of
a morphism `V_{/Z} ⟶ W` into a formal algebraic space `W` follows from the version proved
here together with `CategoryTheory.Subfunctor.sheafifyLift`; what is *not* done here is that
last transport across the sheafification adjunction.

The glueing device used here is `AlgebraicGeometry.Space.glueHom`, which holds at an
unrestricted value universe; a completion is a subfunctor of a presheaf of `Type (u + 1)`
rather than of the hom universe of the site.

## References

* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0GHG](https://stacks.math.columbia.edu/tag/0GHG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The completions of a covering family cover the completion -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If `b ≫ g = c` and `c` has all its points in `ZY`, then `b` has all its points in the
inverse image `ZX` of `ZY` under `g`. -/
private theorem hasImageIn_of_comp_eq {X Y : BigFppfOver B S hS} (g : X ⟶ Y)
    {ZY : Set (points B S hS (yoneda.obj Y))} {ZX : Set (points B S hS (yoneda.obj X))}
    (hZ : ZX = pointsMap B S hS (yoneda.obj X) (yoneda.map g) ⁻¹' ZY)
    {T : BigFppfOver B S hS} {b : T ⟶ X} {c : T ⟶ Y} (hb : b ≫ g = c)
    (hc : HasImageIn B S hS (yoneda.obj Y) ZY T c) :
    HasImageIn B S hS (yoneda.obj X) ZX T b := by
  intro p
  rw [hZ, Set.mem_preimage]
  refine Set.mem_of_eq_of_mem (congrArg (fun v => (⟨p.carrier, p.contained, p.toBase, v⟩ :
    FieldValuedPoint B S hS (yoneda.obj Y)).class B S hS (yoneda.obj Y)) ?_) (hc p)
  exact (Category.assoc _ _ _).trans (congrArg (p.value ≫ ·) hb)

/-- **The missing covering statement for completions.** Let `{V_i ⟶ V}` generate a covering
sieve of the big fppf site over `S`, let `Z` be a set of points of `V` and let `Z_i` be its
inverse image in `V_i`. Then the family of completion subfunctors
`{V_{i,/Z_i} ⟶ V_{/Z}}` generates a covering sieve of sections of `V_{/Z}` at every object of
the site: this is the hypothesis of `AlgebraicGeometry.Space.glueHom`.

As for open subspaces, the condition cutting out the completion is inherited by a lift for
free: a section `b` of `V_i` over `T` whose composition with `V_i ⟶ V` has all its points in
`Z` has all its own points in the inverse image `Z_i`. No hypothesis on `Z` is needed. -/
theorem familyImage_sieveOfSection_mem_completionSubfunctor {V : BigFppfOver B S hS}
    {I : Type*} (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    (Z : Set (points B S hS (yoneda.obj V)))
    (Zi : ∀ i, Set (points B S hS (yoneda.obj (Vi i))))
    (hZi : ∀ i, Zi i = pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)
    (T : BigFppfOver B S hS)
    (x : (completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor.obj (Opposite.op T)) :
    (familyImage fun i => completionSubfunctorRestrict B S hS (yoneda.map (f i)) (Zi i) Z
        (hZi i).subset).sieveOfSection x ∈ BigFppfOver.topology B S hS T := by
  obtain ⟨R, hR, hlift⟩ :=
    exists_lift_of_ofArrows_mem_topology B S hS Vi f hf (T := T) x.1.down
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hR
  intro T' g hg
  obtain ⟨i, b, hb⟩ := hlift hg
  have hbmem : HasImageIn B S hS (yoneda.obj (Vi i)) (Zi i) T' b :=
    hasImageIn_of_comp_eq B S hS (f i) (hZi i) (c := g ≫ x.1.down) hb
      fun p => by simpa using x.2 (⟨p.carrier, p.contained, p.toBase, p.value ≫ g⟩ :
        FieldValuedPoint B S hS (yoneda.obj T))
  exact ⟨i, ⟨ULift.up b, hbmem⟩, Subtype.ext (congrArg ULift.up hb)⟩

/-- **Agreement on overlaps gives the glueing compatibility, for completions.** This is
`AlgebraicGeometry.Space.compatible_of_overlap_openSubspaceOfPoints` for the completion
subfunctors of Stacks 0AMC in place of the open subspaces: if the objects `P i j` of the site
receive two morphisms through which every pair of morphisms agreeing over `V` factors — the
fibre products `V_i ×_V V_j`, which Stacks 0GE1 part (3) keeps inside the locally Noetherian
site — and the two restrictions of `φ i` and `φ j` to the completion of `P i j` agree, then the
compatibility hypothesis of `AlgebraicGeometry.Space.glueHom` holds. -/
theorem compatible_of_overlap_completionSubfunctor {V : BigFppfOver B S hS} {I : Type*}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (Z : Set (points B S hS (yoneda.obj V)))
    (Zi : ∀ i, Set (points B S hS (yoneda.obj (Vi i))))
    (hZi : ∀ i, Zi i = pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (φ : ∀ i, (completionSubfunctor B S hS (yoneda.obj (Vi i)) (Zi i)).toFunctor ⟶ Q)
    (P : I → I → BigFppfOver B S hS) (pr₁ : ∀ i j, P i j ⟶ Vi i) (pr₂ : ∀ i j, P i j ⟶ Vi j)
    (Zij : ∀ i j, Set (points B S hS (yoneda.obj (P i j))))
    (hZij₁ : ∀ i j, Zij i j =
      pointsMap B S hS (yoneda.obj (P i j)) (yoneda.map (pr₁ i j)) ⁻¹' Zi i)
    (hZij₂ : ∀ i j, Zij i j =
      pointsMap B S hS (yoneda.obj (P i j)) (yoneda.map (pr₂ i j)) ⁻¹' Zi j)
    (hlift : ∀ (i j : I) (Y : BigFppfOver B S hS) (a : Y ⟶ Vi i) (b : Y ⟶ Vi j),
      a ≫ f i = b ≫ f j → ∃ h : Y ⟶ P i j, h ≫ pr₁ i j = a ∧ h ≫ pr₂ i j = b)
    (hagree : ∀ i j,
      completionSubfunctorRestrict B S hS (yoneda.map (pr₁ i j)) (Zij i j) (Zi i)
          (hZij₁ i j).subset ≫ φ i =
        completionSubfunctorRestrict B S hS (yoneda.map (pr₂ i j)) (Zij i j) (Zi j)
          (hZij₂ i j).subset ≫ φ j) :
    ∀ (Y : (BigFppfOver B S hS)ᵒᵖ) (i j : I)
      (y : (completionSubfunctor B S hS (yoneda.obj (Vi i)) (Zi i)).toFunctor.obj Y)
      (y' : (completionSubfunctor B S hS (yoneda.obj (Vi j)) (Zi j)).toFunctor.obj Y),
      (completionSubfunctorRestrict B S hS (yoneda.map (f i)) (Zi i) Z
          (hZi i).subset).app Y y =
        (completionSubfunctorRestrict B S hS (yoneda.map (f j)) (Zi j) Z
          (hZi j).subset).app Y y' →
        (φ i).app Y y = (φ j).app Y y' := by
  intro Y
  obtain ⟨T⟩ := Y
  intro i j y y' hy
  have hcomm : y.1.down ≫ f i = y'.1.down ≫ f j :=
    congrArg (fun z => ULift.down (Subtype.val z)) hy
  obtain ⟨h, h₁, h₂⟩ := hlift i j T y.1.down y'.1.down hcomm
  have hmem : HasImageIn B S hS (yoneda.obj (P i j)) (Zij i j) T h :=
    hasImageIn_of_comp_eq B S hS (pr₁ i j) (hZij₁ i j) h₁ y.2
  have hy₁ : (completionSubfunctorRestrict B S hS (yoneda.map (pr₁ i j)) (Zij i j) (Zi i)
      (hZij₁ i j).subset).app (Opposite.op T) ⟨ULift.up h, hmem⟩ = y :=
    Subtype.ext (congrArg ULift.up h₁)
  have hy₂ : (completionSubfunctorRestrict B S hS (yoneda.map (pr₂ i j)) (Zij i j) (Zi j)
      (hZij₂ i j).subset).app (Opposite.op T) ⟨ULift.up h, hmem⟩ = y' :=
    Subtype.ext (congrArg ULift.up h₂)
  rw [← hy₁, ← hy₂]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (hagree i j) (Opposite.op T)) ⟨ULift.up h, hmem⟩

/-- **Glueing a morphism out of a completion along a set of points.** A compatible family of
morphisms `V_{i,/Z_i} ⟶ Q` into an fppf sheaf of `Type (u + 1)` comes from a unique morphism
`V_{/Z} ⟶ Q`. -/
theorem glueHom_completionSubfunctor {V : BigFppfOver B S hS} {I : Type*}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    (Z : Set (points B S hS (yoneda.obj V)))
    (Zi : ∀ i, Set (points B S hS (yoneda.obj (Vi i))))
    (hZi : ∀ i, Zi i = pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q)
    (φ : ∀ i, (completionSubfunctor B S hS (yoneda.obj (Vi i)) (Zi i)).toFunctor ⟶ Q)
    (hφ : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ) (i j : I)
      (y : (completionSubfunctor B S hS (yoneda.obj (Vi i)) (Zi i)).toFunctor.obj Y)
      (y' : (completionSubfunctor B S hS (yoneda.obj (Vi j)) (Zi j)).toFunctor.obj Y),
      (completionSubfunctorRestrict B S hS (yoneda.map (f i)) (Zi i) Z (hZi i).subset).app Y y =
        (completionSubfunctorRestrict B S hS (yoneda.map (f j)) (Zi j) Z
          (hZi j).subset).app Y y' →
        (φ i).app Y y = (φ j).app Y y') :
    ∃! ψ : (completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor ⟶ Q,
      ∀ i, completionSubfunctorRestrict B S hS (yoneda.map (f i)) (Zi i) Z (hZi i).subset ≫
        ψ = φ i :=
  glueHom _ _
    (familyImage_sieveOfSection_mem_completionSubfunctor B S hS Vi f hf Z Zi hZi) hQ φ hφ

/-- **A morphism out of a completion is determined by its restrictions.** -/
theorem hom_ext_completionSubfunctor {V : BigFppfOver B S hS} {I : Type*}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    (Z : Set (points B S hS (yoneda.obj V)))
    (Zi : ∀ i, Set (points B S hS (yoneda.obj (Vi i))))
    (hZi : ∀ i, Zi i = pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q)
    (ψ ψ' : (completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor ⟶ Q)
    (hψ : ∀ i, completionSubfunctorRestrict B S hS (yoneda.map (f i)) (Zi i) Z
      (hZi i).subset ≫ ψ =
        completionSubfunctorRestrict B S hS (yoneda.map (f i)) (Zi i) Z (hZi i).subset ≫ ψ') :
    ψ = ψ' :=
  hom_ext_of_familyImage_cover _ _
    (familyImage_sieveOfSection_mem_completionSubfunctor B S hS Vi f hf Z Zi hZi) hQ ψ ψ' hψ

end AlgebraicGeometry.Space

end
