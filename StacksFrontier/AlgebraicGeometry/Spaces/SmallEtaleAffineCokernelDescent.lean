module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineOverlaps
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCechSheafCondition

/-!
# Descent along a covering family of the small étale site for a presheaf cokernel

Let a sheaf of modules on a slice of the small étale site of an algebraic space be presented by a
morphism `a` between two coproducts of copies of the structure sheaf, and let `π` exhibit a
presheaf of modules as the cokernel of `a` computed object by object.  This file proves that
restriction to the members of a covering family of an object whose underlying scheme is affine is
*injective* on the sections of that presheaf cokernel, and reduces the sheaf condition for such a
family to the case of a family whose image in schemes is a flat covering family.

Over a single covering morphism `Y ⟶ Z` of objects with affine underlying scheme the sections of
the presheaf cokernel over `Y` are the base change of its sections over `Z` along the induced map
of rings of global functions
(`SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel`, whose bases come from
`AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffineCoeffs`), and the base change carries
`1 ⊗ₜ n` to the restriction of `n`.  Applying this to each member of a finite family separately
turns the vanishing of all the restrictions of a section into the vanishing of `1 ⊗ₜ n` in the
base change along every member; the tensor product commutes with a finite product of rings, so
`1 ⊗ₜ n` vanishes in the base change along the product of the rings of global functions of the
members; and that product is faithfully flat over the ring of global functions on the object
covered, because the family is flat and jointly surjective
(`AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`).

Flatness is free here, in contrast to the fppf site.  A covering sieve of an object of a slice
whose underlying scheme is affine contains a finite family of objects with affine underlying
scheme which is *simultaneously* inside the sieve, covering, and flat in schemes
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le_over`), because an
étale morphism is flat; so the two refinement steps the fppf development has to keep apart, one
producing affine members and one producing a flat family, are a single step.  An arbitrary
covering family is reduced to such a refinement, each of whose members factors through a member
of the given family.

The second half of the file is the other half of the sheaf condition for a covering family, and it
is reduced to the same flat case by the same refinement.  A sheaf condition does not descend along
a refinement by itself — an amalgamation produced over the refinement restricts correctly along
the refined arrows, not along the given ones — but it does once the presheaf is separated for the
covering sieves of the *members* of the given family, which have affine underlying scheme, and
that separatedness is what the injectivity above supplies.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.algebra_isPushout_gamma_of_isPullback`: **the ring of global
  functions on a fibre product of two objects of a slice of the small étale site with affine
  underlying scheme is the tensor product of the rings of global functions of the two factors over
  that of the object they lie over.**
* `AlgebraicGeometry.Space.SmallEtale.isSeparatedFor_affine_of_injective_map`: **separatedness of a
  presheaf for every covering sieve of an object with affine underlying scheme follows from
  injectivity of restriction to the members of the finite covering families of objects with affine
  underlying scheme.**
* `AlgebraicGeometry.Space.SmallEtale.isSheafFor_affine_of_isSheafFor_fppf`: **the sheaf condition
  for a covering family of objects with affine underlying scheme follows from the sheaf condition
  for the finite covering families whose image in schemes is a flat covering family**, given
  separatedness at the objects with affine underlying scheme.
* `AlgebraicGeometry.Space.SmallEtale.injective_map_of_isPresheafCokernel_of_fppf`: **restriction
  to the members of a finite family of objects with affine underlying scheme whose image in schemes
  is a flat covering family is injective on the sections of the presheaf cokernel of a presentation
  over an object with affine underlying scheme.**
* `AlgebraicGeometry.Space.SmallEtale.injective_map_of_isPresheafCokernel`: the same for an
  arbitrary covering family, flatness and affineness of the members no longer being assumed.
* `AlgebraicGeometry.Space.SmallEtale.injective_map_cokernel_of_isAffineOver`: **the same for the
  categorical cokernel of the presenting morphism computed in presheaves of modules.**
* `AlgebraicGeometry.Space.SmallEtale.isSheafFor_cokernel_affine_of_isSheafFor_fppf`: **the sheaf
  condition for the presheaf cokernel of a presentation, for an arbitrary finite covering family of
  objects with affine underlying scheme, reduces to the case of a family which is flat in
  schemes.**

## Implementation notes

The commutative rings are the rings of global functions on the underlying schemes, and the module
structures on the sections over them are the structures over the rings of sections of the
coefficient sheaf of rings, which are the same rings definitionally
(`AlgebraicGeometry.Space.SmallEtale.ringSheaf_over_obj_obj`).  Over a member of the family the
ring of global functions on the object covered acts through the induced map of global functions, so
the restriction maps are linear rather than only semilinear; the algebra structure is the one that
map defines, so the equation identifying its `algebraMap` with it holds by `rfl`.

Two spellings of the objects of the small étale site occur, and the choice is forced in each case.
The purely geometric statements, which assume nothing about a structure sheaf, take a chart of
`AlgebraicGeometry.Space.SmallEtale`, which is the spelling for which the fibre products of a
slice and the covering families are found by instance search; the statements mentioning a sheaf of
modules take an object of the underlying category of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the same type behind a structure
projection and is the spelling for which `CategoryTheory.Category` on a slice, and hence the whole
sheaves-of-modules API, is found.  Mixing the two inside one declaration is what does not work:
instance search type-checks at a transparency which does not unfold the projection, so an
instance found at one spelling does not apply at the other.  Crossing between them happens only
where a statement is *applied*, which is checked at full transparency.

The statements are for a morphism `π` with the property `PresheafOfModules.IsPresheafCokernel`
rather than for the categorical cokernel, which is a `noncomputable` construction and so cannot
appear in the definitions of the module structures the proof introduces; the categorical cokernel
has the property by `PresheafOfModules.isPresheafCokernel_cokernelπ`.

Both coproducts of the presentation carry their tautological generators and the witnesses that
they are coproducts, because the base-change comparison for the presheaf cokernel uses the
generators of the relations as well as the generators of the module.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe z t u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

namespace SmallEtale

section Slice

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C}

/-! ### The rings of the overlaps of a covering family as a pushout -/

/-- **The ring of global functions on a fibre product of two objects of a slice of the small étale
site whose underlying schemes are affine, over an object whose underlying scheme is affine, is the
tensor product of the rings of global functions of the two factors over that of the object they
lie over.**

The square of underlying schemes is a fibre product square
(`AlgebraicGeometry.Space.SmallEtale.isPullback_toScheme_of_isPullback`), so
`AlgebraicGeometry.algebra_isPushout_appTop_of_isPullback` applies to it.

This is the pushout form of
`AlgebraicGeometry.Space.SmallEtale.exists_ringEquivTensorGamma_of_isPullback`, which returns the
same identification as a ring isomorphism together with its two values on pure tensors.  The
pushout form is what the degree-two term of an Amitsur complex is matched against, where the
tensor product of the two rings of the members has to be recognised *as* the ring of the overlap
rather than compared with it.

As everywhere here the algebra structures are the consumer's own, identified with the maps of
global functions by hypothesis. -/
theorem algebra_isPushout_gamma_of_isPullback {W Y D Pb : Over V}
    {fst : Pb ⟶ Y} {snd : Pb ⟶ D} {f : Y ⟶ W} {g : D ⟶ W} (h : IsPullback fst snd f g)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left)))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Y.left)))
    (hD : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj D.left)))
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Y.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj D.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Y.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj D.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤)]
    [IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Y.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤)]
    [IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj D.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤)]
    (hf : algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Y.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map f.left)).appTop.hom)
    (hg : algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj D.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map g.left)).appTop.hom)
    (hfst : algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Y.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map fst.left)).appTop.hom)
    (hsnd : algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj D.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map snd.left)).appTop.hom) :
    Algebra.IsPushout Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Y.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj D.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤) :=
  have _ := hW
  have _ := hY
  have _ := hD
  algebra_isPushout_appTop_of_isPullback
    (isPullback_toScheme_of_isPullback B S hS F h) hf hg hfst hsnd

/-! ### Finite affine flat refinements of a covering sieve -/

/-- **A covering sieve of an object of a slice of the small étale site whose underlying scheme is
affine contains a finite family of objects with affine underlying scheme which is inside the sieve,
covering, and flat in schemes.**

This is `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le_over` with the
object covered given as an object of the slice rather than as a morphism of charts, and with the
objects of the site spelled through the projection of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the spelling the sheaves of modules on the
slice are indexed by.  The two spellings are definitionally equal; restating is what keeps the
whole of the argument below inside one of them, so that instance search, which does not unfold the
projection, succeeds throughout. -/
theorem exists_finite_affine_ofArrows_le_over (Z : Over V)
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left)))
    (T : Sieve Z) (hT : T ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z) :
    ∃ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ Z),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left))) ∧ (∀ i, T (g i)) ∧
        Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z ∧
        Presieve.ofArrows
            (fun i ↦ (BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj (Y i).left))
            (fun i ↦ (BigFppfOver.toScheme B S hS).map
              ((SmallEtale.toOver B S hS F).map (g i).left)) ∈
          Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj Z.left)) :=
  exists_finite_affine_etale_ofArrows_le_over B S hS F Z.hom hZ T hT

/-! ### Separatedness and the sheaf condition at the objects with affine underlying scheme -/

/-- **Separatedness of a presheaf for every covering sieve of an object of a slice of the small
étale site whose underlying scheme is affine follows from injectivity of restriction to the members
of the finite covering families of objects with affine underlying scheme.**

A covering sieve of such an object contains a finite covering family of objects with affine
underlying scheme, by
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le_over`;
separatedness for a family of arrows of a sieve gives separatedness for the sieve
(`CategoryTheory.Presheaf.isSeparatedFor_of_exists_isSeparatedFor_le`); and separatedness for a
family of arrows is injectivity of restriction to its members
(`CategoryTheory.Presieve.isSeparatedFor_ofArrows_of_injective`).

This is the form in which separatedness of a presheaf cokernel is proved: there are no sieves and
no topology left in the hypothesis, only injectivity of a restriction map between the sections over
two objects with affine underlying scheme, which is what a base-change comparison along a flat
covering family supplies. -/
theorem isSeparatedFor_affine_of_injective_map (G : (Over V)ᵒᵖ ⥤ Type z)
    (hinj : ∀ Z : Over V, IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left)) →
      ∀ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ Z),
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left))) →
        Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z →
          Function.Injective fun s : G.obj (op Z) ↦ fun i ↦ G.map (g i).op s)
    (Z : Over V) (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left)))
    (T : Sieve Z) (hT : T ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z) :
    Presieve.IsSeparatedFor G (T : Presieve Z) := by
  obtain ⟨k, Y, g, hYaff, hgT, hgcov, -⟩ :=
    exists_finite_affine_ofArrows_le_over B S hS F hF Z hZ T hT
  exact Presheaf.isSeparatedFor_of_exists_isSeparatedFor_le G T g hgT
    (Presieve.isSeparatedFor_ofArrows_of_injective g (hinj Z hZ k Y g hYaff hgcov))

/-- **The sheaf condition for a covering family of objects of a slice of the small étale site with
affine underlying scheme follows from the sheaf condition for the finite covering families whose
image in schemes is a flat covering family**, given separatedness of the presheaf for the covering
sieves of the objects with affine underlying scheme.

The separatedness is what makes the reduction go, and without it the reduction is false: the
amalgamation the flat case produces over the refinement
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le_over`) restricts
correctly along the arrows of the refinement, which are not the arrows of the given family.  What
repairs that is that the restriction of the amalgamation along a member of the given family, and
the section the family assigns to that member, agree after restriction along every arrow of the
pullback along that member of the sieve generated by the refinement; that pullback is a covering
sieve of an object with affine underlying scheme, and separatedness there identifies the two.
Uniqueness of the amalgamation is separatedness at the object covered.

The given family is not assumed flat, and indeed a finite covering family of objects with affine
underlying scheme of the small étale site need not consist of flat morphisms of schemes: the
morphisms of the site are étale over the base, not over each other. -/
theorem isSheafFor_affine_of_isSheafFor_fppf (G : (Over V)ᵒᵖ ⥤ Type z)
    (hsep : ∀ Z : Over V, IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left)) →
      ∀ T : Sieve Z, T ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z →
        Presieve.IsSeparatedFor G (T : Presieve Z))
    (W : Over V) (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left)))
    (hfppf : ∀ (k : ℕ) (Y' : Fin k → Over V) (g' : ∀ j, Y' j ⟶ W),
      (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y' j).left))) →
      Sieve.ofArrows Y' g' ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) W →
      Presieve.ofArrows
          (fun j ↦ (BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj (Y' j).left))
          (fun j ↦ (BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS F).map (g' j).left)) ∈
        Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left)) →
        Presieve.IsSheafFor G (Presieve.ofArrows Y' g'))
    {ιi : Type*} (Y : ιi → Over V) (g : ∀ i, Y i ⟶ W)
    (hY : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y i).left)))
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) W) :
    Presieve.IsSheafFor G (Presieve.ofArrows Y g) := by
  have mc : ∀ {U U' U'' : Over V} (α : U ⟶ U') (β : U' ⟶ U'') (t : G.obj (op U'')),
      G.map α.op (G.map β.op t) = G.map (α ≫ β).op t := fun α β t ↦
    (Functor.map_comp_apply G β.op α.op t).symm
  obtain ⟨k, Y', g', hY'aff, hmem, hcov', hfp⟩ :=
    exists_finite_affine_ofArrows_le_over B S hS F hF W hW (Sieve.ofArrows Y g) hcov
  choose σ hh hfac using fun j ↦ (Sieve.mem_ofArrows_iff _ _ _).1 (hmem j)
  rw [Presieve.isSheafFor_arrows_iff]
  intro s hs
  have hs' : Presieve.Arrows.Compatible G g' fun j ↦ G.map (hh j).op (s (σ j)) := by
    intro j₁ j₂ Z₀ k₁ k₂ hk
    have hcc : (k₁ ≫ hh j₁) ≫ g (σ j₁) = (k₂ ≫ hh j₂) ≫ g (σ j₂) := by
      rw [Category.assoc, Category.assoc, ← hfac j₁, ← hfac j₂]; exact hk
    rw [mc k₁ (hh j₁), mc k₂ (hh j₂)]
    exact hs (σ j₁) (σ j₂) Z₀ (k₁ ≫ hh j₁) (k₂ ≫ hh j₂) hcc
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff ..).1
    (hfppf k Y' g' hY'aff hcov' hfp) _ hs'
  have key : ∀ i, G.map (g i).op t = s i := by
    intro i
    refine (hsep (Y i) (hY i) ((Sieve.ofArrows Y' g').pullback (g i))
      (((smallEtaleRingedSite B S hS F hF).J.over V).pullback_stable _ hcov')).ext ?_
    intro Z₀ f hf
    obtain ⟨j, c, hc⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
    have hcomp : (c ≫ hh j) ≫ g (σ j) = f ≫ g i := by
      rw [Category.assoc, ← hfac j, ← hc]
    have h1 : G.map f.op (G.map (g i).op t) = G.map (c ≫ hh j).op (s (σ j)) := by
      rw [mc f (g i) t, hc, ← mc c (g' j) t, ht j, mc c (hh j) (s (σ j))]
    rw [h1, hs (σ j) i Z₀ (c ≫ hh j) f hcomp]
  refine ⟨t, key, ?_⟩
  show ∀ t' : G.obj (op W), (∀ i, G.map (g i).op t' = s i) → t' = t
  intro t' ht'
  refine (hsep W hW (Sieve.ofArrows Y g) hcov).ext ?_
  intro Z₀ f hf
  obtain ⟨i, b, hb⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  rw [hb, ← mc b (g i) t', ← mc b (g i) t, ht' i, key i]

end Slice

/-! ### Injectivity of restriction on the sections of a presheaf cokernel -/

section Injectivity

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C} {K I : Type z}
  {Q P : SheafOfModules.{max t u}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
  {N : PresheafOfModules.{max t u}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V).obj}
  (κ : ∀ _ : K, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
    (SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ Q)
  (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
    (SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ P)
  (hQ : IsColimit (Cofan.mk Q κ)) (hP : IsColimit (Cofan.mk P ι))
  (a : Q ⟶ P) (π : P.val ⟶ N) (hπ : PresheafOfModules.IsPresheafCokernel a.val π)

include κ ι hQ hP hπ in
/-- **Restriction to the members of a finite family of objects with affine underlying scheme whose
image in schemes is a flat covering family is injective on the sections of the presheaf cokernel of
a presentation over an object with affine underlying scheme.**

Member by member the sections of the presheaf cokernel over a member are the base change of its
sections over the object covered
(`SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel`, with the four bases supplied by
`AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffineCoeffs`); the product of the rings of global
functions on the members is faithfully flat over the ring of global functions on the object covered
(`AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`); and
`PresheafOfModules.injective_map_of_forall_injective_baseChange` combines the two.

Neither a coproduct of the family inside the site nor the first cohomology of anything occurs:
what replaces the coproduct is the finite product of the rings of global functions. -/
theorem injective_map_of_isPresheafCokernel_of_fppf {ιi : Type*} [Finite ιi] (Z : Over V)
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left)))
    (Y : ιi → Over V) (g : ∀ i, Y i ⟶ Z)
    (hY : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y i).left)))
    (hfppf : Presieve.ofArrows
        (fun i ↦ (BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map (g i).left)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left))) :
    Function.Injective fun n : N.obj (op Z) ↦ fun i ↦ N.map (g i).op n := by
  let alg : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤) := fun i ↦
    RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (g i).left)).appTop.hom
  have hff : Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
      (∀ i, Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)) :=
    faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage B S hS F Y g hZ hY hfppf fun _ ↦ rfl
  let R := ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V
  let mZ : ∀ M : PresheafOfModules.{max t u} R.obj,
      Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) (M.obj (op Z)) := fun M ↦
    inferInstanceAs (Module (R.obj.obj (op Z)) (M.obj (op Z)))
  let mY : ∀ (M : PresheafOfModules.{max t u} R.obj) i,
      Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤) (M.obj (op (Y i))) := fun M i ↦
    inferInstanceAs (Module (R.obj.obj (op (Y i))) (M.obj (op (Y i))))
  let mY' : ∀ (M : PresheafOfModules.{max t u} R.obj) i,
      Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) (M.obj (op (Y i))) := fun M i ↦
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤))
  have tw : ∀ (M : PresheafOfModules.{max t u} R.obj) i,
      IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤) (M.obj (op (Y i))) :=
    fun _ _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hall : ∀ i, ∃ e : Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)
      ⊗[Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)] (N.obj (op Z))
      ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)] (N.obj (op (Y i))),
      ∀ n, e ((1 : Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)) ⊗ₜ n)
        = N.restrictₛₗ (g i).op n := fun i ↦
    SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel (N := N) κ ι (g i)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)
      (tautBasisOfIsAffineCoeffs B S hS F hF κ hQ Z hZ
        (sectionRingEquivGamma B S hS F hF Z) (fun _ _ ↦ rfl))
      (tautBasisOfIsAffineCoeffs B S hS F hF κ hQ (Y i) (hY i)
        (sectionRingEquivGamma B S hS F hF (Y i)) (fun _ _ ↦ rfl))
      (tautBasisOfIsAffineCoeffs B S hS F hF ι hP Z hZ
        (sectionRingEquivGamma B S hS F hF Z) (fun _ _ ↦ rfl))
      (tautBasisOfIsAffineCoeffs B S hS F hF ι hP (Y i) (hY i)
        (sectionRingEquivGamma B S hS F hF (Y i)) (fun _ _ ↦ rfl))
      (fun k ↦ tautBasisOfIsAffineCoeffs_apply B S hS F hF κ hQ Z hZ _ _ k)
      (fun k ↦ tautBasisOfIsAffineCoeffs_apply B S hS F hF κ hQ (Y i) (hY i) _ _ k)
      (fun j ↦ tautBasisOfIsAffineCoeffs_apply B S hS F hF ι hP Z hZ _ _ j)
      (fun j ↦ tautBasisOfIsAffineCoeffs_apply B S hS F hF ι hP (Y i) (hY i) _ _ j)
      { toFun := fun q ↦ Q.val.map (g i).op q
        map_add' := map_add (Q.val.map (g i).op).hom
        map_smul' := fun c q ↦ (Q.val.map_smul (g i).op c q).symm ▸ rfl }
      (fun _ ↦ rfl)
      { toFun := fun q ↦ P.val.map (g i).op q
        map_add' := map_add (P.val.map (g i).op).hom
        map_smul' := fun c q ↦ (P.val.map_smul (g i).op c q).symm ▸ rfl }
      (fun _ ↦ rfl)
      { toFun := fun n ↦ N.map (g i).op n
        map_add' := map_add (N.map (g i).op).hom
        map_smul' := fun c n ↦ (N.map_smul (g i).op c n).symm ▸ rfl }
      (fun _ ↦ rfl) a π hπ
      (a.val.app (op Z)).hom (fun _ ↦ rfl)
      (π.app (op Z)).hom (fun _ ↦ rfl)
      (a.val.app (op (Y i))).hom (fun _ ↦ rfl)
      (π.app (op (Y i))).hom (fun _ ↦ rfl)
  choose e he using hall
  exact PresheafOfModules.injective_map_of_forall_injective_baseChange g
    Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
    (fun i ↦ Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤))
    (fun i ↦ (e i).toLinearMap.toAddMonoidHom) (fun i ↦ (e i).injective) he

include κ ι hQ hP hπ in
/-- **Restriction to the members of a covering family of an object with affine underlying scheme is
injective on the sections of the presheaf cokernel of a presentation.**  Neither affineness nor
flatness of the members is assumed.

A covering sieve of such an object contains a finite family of objects with affine underlying
scheme whose image in schemes is a flat covering family
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le_over`), for which
`AlgebraicGeometry.Space.SmallEtale.injective_map_of_isPresheafCokernel_of_fppf` applies; and every
member of that refinement factors through a member of the given family, so a section whose
restrictions along the given family agree has agreeing restrictions along the refinement.

One refinement suffices, in contrast to the fppf site: a morphism of the small étale site is étale,
hence flat, so the refinement by objects with affine underlying scheme is a flat family of schemes
at the same time, and there is no second step. -/
theorem injective_map_of_isPresheafCokernel (Z : Over V)
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left)))
    {ιi : Type*} (Y : ιi → Over V) (g : ∀ i, Y i ⟶ Z)
    (hcov : Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z) :
    Function.Injective fun n : N.obj (op Z) ↦ fun i ↦ N.map (g i).op n := by
  obtain ⟨k, Y', g', hY'aff, hmem, -, hfppf⟩ :=
    exists_finite_affine_ofArrows_le_over B S hS F hF Z hZ (Sieve.ofArrows Y g) hcov
  intro s s' hss'
  refine injective_map_of_isPresheafCokernel_of_fppf B S hS F hF κ ι hQ hP a π hπ Z hZ Y' g'
    hY'aff hfppf (funext fun j ↦ ?_)
  obtain ⟨i, hh, hfac⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 (hmem j)
  have key : ∀ n : N.obj (op Z), N.map (g' j).op n = N.map hh.op (N.map (g i).op n) := fun n ↦ by
    rw [hfac]; exact N.map_comp_apply (g i).op hh.op n
  show N.map (g' j).op s = N.map (g' j).op s'
  have h0 : N.map (g i).op s = N.map (g i).op s' := congrFun hss' i
  rw [key s, key s', h0]

end Injectivity

/-! ### The two hypotheses of the surjectivity criterion for the categorical cokernel -/

section Cokernel

variable (hF : IsAlgebraicSpace B S hS F) {V : (smallEtaleRingedSite B S hS F hF).C} {K I : Type z}
  {Q P : SheafOfModules.{max t u}
    (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)}
  (κ : ∀ _ : K, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
    (SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ Q)
  (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{u + 1, u, u, u, t}
    (SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) ⟶ P)
  (hQ : IsColimit (Cofan.mk Q κ)) (hP : IsColimit (Cofan.mk P ι)) (a : Q ⟶ P)

include κ ι hQ hP in
/-- **Restriction to the members of a finite covering family of objects with affine underlying
scheme is injective on the sections, over an object with affine underlying scheme, of the cokernel
of a presenting morphism computed in presheaves of modules.**

This is `AlgebraicGeometry.Space.SmallEtale.injective_map_of_isPresheafCokernel` for the
categorical cokernel, whose projection has the required property by
`PresheafOfModules.isPresheafCokernel_cokernelπ`.  It is stated in the shape the surjectivity
criterion asks for it: no sieve and no topology occurs beyond membership of one covering family,
and affineness of the members, which the refinement supplies for itself, is not used. -/
theorem injective_map_cokernel_of_isAffineOver :
    ∀ Z : Over V, IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left)) →
      ∀ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ Z),
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left))) →
        Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) Z →
          Function.Injective fun s : (cokernel a.val).obj (op Z) ↦
            fun i ↦ (cokernel a.val).map (g i).op s :=
  fun Z hZ _ Y g _ hcov ↦
    injective_map_of_isPresheafCokernel B S hS F hF κ ι hQ hP a (cokernel.π a.val)
      (PresheafOfModules.isPresheafCokernel_cokernelπ a.val) Z hZ Y g hcov

include κ ι hQ hP in
/-- **The sheaf condition for the cokernel of a presenting morphism computed in presheaves of
modules, for an arbitrary finite covering family of objects with affine underlying scheme, reduces
to the case of a family which is flat in schemes.**

This is `AlgebraicGeometry.Space.SmallEtale.isSheafFor_affine_of_isSheafFor_fppf` for that presheaf
cokernel, whose separatedness hypothesis at the objects with affine underlying scheme is discharged
by `AlgebraicGeometry.Space.SmallEtale.isSeparatedFor_affine_of_injective_map` from
`AlgebraicGeometry.Space.SmallEtale.injective_map_cokernel_of_isAffineOver`.

So the whole of what the cokernel step of a global presentation still asks for is the sheaf
condition for one finite covering family of objects with affine underlying scheme whose image in
schemes is a flat covering family, which is what
`PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀` computes from the Amitsur complex of the
product of the rings of global functions on the members. -/
theorem isSheafFor_cokernel_affine_of_isSheafFor_fppf (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left)))
    (hfppf : ∀ (k : ℕ) (Y' : Fin k → Over V) (g' : ∀ j, Y' j ⟶ W),
      (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y' j).left))) →
      Sieve.ofArrows Y' g' ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) W →
      Presieve.ofArrows
          (fun j ↦ (BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj (Y' j).left))
          (fun j ↦ (BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS F).map (g' j).left)) ∈
        Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left)) →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max t u})
          (Presieve.ofArrows Y' g')) :
    ∀ (k : ℕ) (Y : Fin k → Over V) (g : ∀ i, Y i ⟶ W),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left))) →
      Sieve.ofArrows Y g ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) W →
        Presieve.IsSheafFor
          ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max t u})
          (Presieve.ofArrows Y g) :=
  fun _ Y g hY hcov ↦
    isSheafFor_affine_of_isSheafFor_fppf B S hS F hF _
      (fun Z hZ T hT ↦ isSeparatedFor_affine_of_injective_map B S hS F hF _
        (injective_map_cokernel_of_isAffineOver B S hS F hF κ ι hQ hP a) Z hZ T hT)
      W hW hfppf Y g hY hcov

end Cokernel

end SmallEtale

end AlgebraicGeometry.Space

end
