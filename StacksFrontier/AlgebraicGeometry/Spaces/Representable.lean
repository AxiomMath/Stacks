module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalRepresentable

/-!
# Representable transformations of presheaves on a big fppf site

A transformation `a : F ⟶ G` of presheaves of sets on the big fppf site of a scheme `S` is
*representable* when it is relatively representable along the Yoneda embedding of that site,
in the sense of `CategoryTheory.Functor.relativelyRepresentable`: every base change of `a`
by a representable presheaf is representable.

For the Yoneda embedding of any category with fibre products, a morphism `f : X ⟶ Y` induces a
representable transformation `h_f : h_X ⟶ h_Y`, and representable transformations are stable
under composition and under base change.

## Main definitions

* `AlgebraicGeometry.compatibleFamilyToNatTrans`: a compatible family of sections of `P` on a
  sieve `R`, as a transformation `R.functor ⟶ P`.

## Main results

* `CategoryTheory.MorphismProperty.presheaf_id`: an identity morphism of presheaves satisfies
  the presheaf property attached to a morphism property which contains the identities and
  respects isomorphisms.
* `AlgebraicGeometry.relativelyRepresentable_diag_yoneda_obj`: the diagonal of a representable
  presheaf on the big fppf site of `S` is representable.
* `AlgebraicGeometry.relativelyRepresentable_pullback_diagonal`: the relative diagonal of a
  representable transformation is representable.
* `AlgebraicGeometry.isSheaf_of_forall_isSheaf_pullback`: if `G` is a sheaf and every base change
  of `a : F ⟶ G` by a representable presheaf is a sheaf, then `F` is a sheaf.
* `AlgebraicGeometry.isSheaf_of_relativelyRepresentable`: the source of a representable
  transformation into a sheaf is a sheaf.
* `AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable`: the source of a representable
  transformation into an algebraic space is an algebraic space.

## References

* [Stacks Project, Tag 02W9](https://stacks.math.columbia.edu/tag/02W9)
* [Stacks Project, Tag 02WA](https://stacks.math.columbia.edu/tag/02WA)
* [Stacks Project, Tag 02WB](https://stacks.math.columbia.edu/tag/02WB)
* [Stacks Project, Tag 05L9](https://stacks.math.columbia.edu/tag/05L9)
* [Stacks Project, Tag 02WD](https://stacks.math.columbia.edu/tag/02WD)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

add_to_stacks 02W9
  "for the Yoneda embedding of a category with fibre products, `h_f` is representable"
  CategoryTheory.Functor.relativelyRepresentable.map

add_to_stacks 02WA "representable transformations are stable under composition"
  CategoryTheory.Functor.relativelyRepresentable.isMultiplicative

add_to_stacks 02WB "representable transformations are stable under base change"
  CategoryTheory.Functor.relativelyRepresentable.isStableUnderBaseChange

namespace CategoryTheory.MorphismProperty

/-- An identity morphism of presheaves satisfies the presheaf property attached to a
morphism property containing the identities and respecting isomorphisms. -/
theorem presheaf_id {C : Type u} [Category.{v} C] (P : MorphismProperty C)
    [P.ContainsIdentities] [P.RespectsIso] (F : Cᵒᵖ ⥤ Type v) : P.presheaf (𝟙 F) :=
  relative.of_exists fun a g ↦
    ⟨a, g, 𝟙 a, by simpa using IsPullback.of_id_snd, P.id_mem a⟩

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

/-- The diagonal of a representable presheaf on the big fppf site of `S` is representable. -/
theorem relativelyRepresentable_diag_yoneda_obj
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS) :
    yoneda.relativelyRepresentable (diag (yoneda.obj U)) := by
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  refine Functor.relativelyRepresentable.diag_of_map_from_obj fun a g ↦ ?_
  obtain ⟨g, rfl⟩ := yoneda.map_surjective g
  exact Functor.relativelyRepresentable.map yoneda g

/-- The relative diagonal of a representable transformation of presheaves on the big fppf site
over `S` is representable. -/
alias relativelyRepresentable_pullback_diagonal :=
    AlgebraicGeometry.Space.relativelyRepresentable_diagonal_of_representable

section Sheaf

universe u₁ v₁

/-- The diagonal of a presheaf is representable iff the diagonal of its map to the terminal
presheaf is. -/
private theorem relativelyRepresentable_diag_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    yoneda.relativelyRepresentable (diag F) ↔
      yoneda.relativelyRepresentable (pullback.diagonal (terminal.from F)) := by
  have heq : diag F = pullback.diagonal (terminal.from F) ≫ (prodIsoPullback F F).inv := by
    cat_disch
  rw [heq]
  exact (MorphismProperty.cancel_right_of_respectsIso
    (P := yoneda.relativelyRepresentable) _ _)

/-- The big fppf site over `S` has a subcanonical topology. -/
private theorem subcanonical_topology_bigFppfOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigFppfOver.topology B S hS).Subcanonical :=
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  inferInstanceAs (B.topology.over (B.obj hS)).Subcanonical

/-- A compatible family of sections of a presheaf `P` on a sieve `R` of `X`, read as a
transformation from the functor of `R` to `P`. -/
public def compatibleFamilyToNatTrans {C : Type u₁} [Category.{v₁, u₁} C]
    {X : C} {P : Cᵒᵖ ⥤ Type v₁} (R : Sieve X)
    (x : Presieve.FamilyOfElements P R.arrows) (hx : x.Compatible) :
    R.functor ⟶ P where
  app Y := ↾fun g ↦ x g.1 g.2
  naturality := by
    intro Y Z f
    ext g
    change x (f.unop ≫ g.1) _ = P.map f (x g.1 g.2)
    simpa using (Presieve.compatible_iff_sieveCompatible x).1 hx g.1 f.unop g.2

/-- Let `a : F ⟶ G` be a transformation of presheaves on the big fppf site over `S` into a
sheaf `G`. If the base change of `a` along every morphism from a representable presheaf is a
sheaf, then `F` is a sheaf. -/
theorem isSheaf_of_forall_isSheaf_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (hpb : ∀ (X : BigFppfOver B S hS) (v : yoneda.obj X ⟶ G),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback v a))
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) F := by
  let J := BigFppfOver.topology B S hS
  have : J.Subcanonical := subcanonical_topology_bigFppfOver B S hS
  have hG' : Presieve.IsSheaf J G :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type J G).1 hG
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  intro X R hR s hs
  let fNat : R.functor ⟶ F := compatibleFamilyToNatTrans R s hs
  obtain ⟨gG, hgG, hgGuniq⟩ :=
    Presieve.isSheafFor_iff_yonedaSheafCondition.1 (hG' R hR) (fNat ≫ a)
  let H := pullback gG a
  have hH' : Presieve.IsSheaf J H :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type J H).1 (hpb X gG)
  let k : R.functor ⟶ H := pullback.lift R.functorInclusion fNat hgG
  obtain ⟨gH, hgH, hgHuniq⟩ := Presieve.isSheafFor_iff_yonedaSheafCondition.1 (hH' R hR) k
  let t₀ := yonedaEquiv (gH ≫ pullback.snd gG a)
  refine ⟨t₀, ?_, ?_⟩
  · intro Y f hf
    have hres : R.functorInclusion ≫ (gH ≫ pullback.snd gG a) = fNat := by
      rw [← Category.assoc, hgH, pullback.lift_snd]
    have heq := congrArg (fun q : R.functor ⟶ F => q.app (Opposite.op Y) ⟨f, hf⟩) hres
    change (pullback.snd gG a).app (Opposite.op Y) (gH.app (Opposite.op Y) f) =
      (fNat.app (Opposite.op Y)) ⟨f, hf⟩ at heq
    simpa [t₀, fNat, compatibleFamilyToNatTrans, CategoryTheory.map_yonedaEquiv] using heq
  · intro t ht
    let tYon : yoneda.obj X ⟶ F := yonedaEquiv.symm t
    have htrestrict : R.functorInclusion ≫ tYon = fNat := by
      ext Y z
      rcases z with ⟨f, hf⟩
      change F.map f.op t = fNat.app Y ⟨f, hf⟩
      simpa [fNat, compatibleFamilyToNatTrans] using ht f hf
    have hta : tYon ≫ a = gG :=
      hgGuniq (tYon ≫ a) <| by
        simpa [Category.assoc] using congrArg (fun q : R.functor ⟶ F => q ≫ a) htrestrict
    let k' : yoneda.obj X ⟶ H := pullback.lift (𝟙 (yoneda.obj X)) tYon (by
      rw [Category.id_comp, hta])
    have hk' : R.functorInclusion ≫ k' = k := by
      apply pullback.hom_ext <;>
        simp only [Category.assoc, k', k, pullback.lift_fst, pullback.lift_snd,
          Category.comp_id, htrestrict]
    have hkeq := hgHuniq k' hk'
    have hmap : tYon = gH ≫ pullback.snd gG a := by
      have hh := congrArg (fun q => q ≫ pullback.snd gG a) hkeq
      dsimp only [k'] at hh
      simpa only [pullback.lift_snd] using hh
    simpa [tYon, t₀] using congrArg yonedaEquiv hmap

/-- A representable transformation into a sheaf on the big fppf site over `S` has a sheaf as
its source. -/
theorem isSheaf_of_relativelyRepresentable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : yoneda.relativelyRepresentable a)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) F := by
  have := subcanonical_topology_bigFppfOver B S hS
  refine isSheaf_of_forall_isSheaf_pullback B S hS a (fun X v => ?_) hG
  have : (pullback v a).IsRepresentable := by
    simpa using
      (CategoryTheory.yoneda_relativelyRepresentable_iff_pullback_representable a).1 ha X
        (yonedaEquiv v)
  exact (CategoryTheory.isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) _).2
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end Sheaf

/-- A representable transformation to an algebraic space over `S` has an
algebraic space over `S` as its source. -/
@[stacks 02WY]
theorem isAlgebraicSpace_of_relativelyRepresentable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : G ⟶ F) (ha : yoneda.relativelyRepresentable a)
    (hF : IsAlgebraicSpace B S hS F) :
    IsAlgebraicSpace B S hS G := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    yoneda.relativelyRepresentable
  have hdiag : P (diag G) := by
    refine (relativelyRepresentable_diag_iff B S hS G).2 ?_
    simpa only [MorphismProperty.diagonal_iff, terminal.comp_from] using
      (MorphismProperty.comp_mem P.diagonal a (terminal.from F)
        (relativelyRepresentable_pullback_diagonal B S hS a ha)
        ((relativelyRepresentable_diag_iff B S hS F).1 hF.diagonal_representable))
  obtain ⟨U, f, hfSurjective, hfEtale⟩ := hF.exists_atlas
  obtain ⟨U', s', t', hpb⟩ := ha f
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  refine ⟨isSheaf_of_relativelyRepresentable B S hS a ha hF.isSheaf,
    hdiag, U', t', ?_, ?_⟩
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hfSurjective
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hfEtale

end AlgebraicGeometry

end
