module

public import StacksFrontier.CategoryTheory.Sites.Topos.InverseImageSolutionComparison

/-!
# The inverse image of a sheaf of solutions is again a sheaf of solutions

Let `(g, g^♯) : (Sh(C), 𝒪') ⟶ (Sh(D), 𝒪)` be a morphism of ringed topoi and let `H` be a sheaf
downstairs cut out of `∏ᵏ 𝒪` as the equalizer of the row `∏ᵏ 𝒪 ⇉ ∏ᵛ 𝒪` of a polynomial system
`P₁, …, P_ν` in `κ` variables.  This file is the *exactness* half of step (3) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6): because `g⁻¹` is left
exact and the equalizer is a finite limit, `g⁻¹H` is again the equalizer of the row of the same
system `P`, read over the inverse image `g⁻¹𝒪` of the structure sheaf downstairs.

Two things have to happen for that to be a statement about a row of the shape the rest of the
development uses.  First, `g⁻¹` does not literally carry `∏ᵏ 𝒪` to `∏ᵏ g⁻¹𝒪`; it carries it to
a product cone whose comparison map `piComparison` is an isomorphism, which it is because `κ`
is finite and `g⁻¹` preserves finite limits.  Second, the two legs of the row have to be
recognized, after this transport, as the legs of the row of `P` over `g⁻¹𝒪` with the
*sectionwise* commutative ring object structure of
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf`; that recognition is
`Stacks.Sheaves.inverseImage_map_evalSystemHom_pullback` and its companion for the zero leg.

Note what this is **not**.  It is not the assertion that the comparison morphism
`Stacks.Sheaves.inverseImageForkComparison` into the sheaf of solutions over `𝒪'` is an
isomorphism.  That morphism is, by construction, the canonical map of equalizers induced by the
structure map `α : g⁻¹𝒪 ⟶ 𝒪'` — which is the content of
`Stacks.Sheaves.inverseImageForkComparison_eq_lift` below — and a canonical map of equalizers
induced by a map of the two rows is not invertible merely because both rows are equalizers;
`α` is not an isomorphism.  In the source, invertibility is a *separate* argument (step (4)):
the small étale site has enough points, and on stalks the map is the bijection between the
solutions of an étale system over two strictly henselian local rings along a local homomorphism,
which is [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX).  What this file
supplies for that argument is its first input: the identification of `g⁻¹H` as the sheaf of
solutions of `P` over `g⁻¹𝒪`, which is what makes its stalk a set of solutions at all.

Accordingly nothing here carries an `@[stacks 04I6]` tag: that tag asserts a 2-isomorphism of
morphisms of ringed topoi together with its uniqueness, and this is one step inside its proof.

## Main results

* `Stacks.Sheaves.inverseImagePullbackCoordinates_comp_evalSystemHom`: the pulled-back
  coordinates of `g⁻¹H` solve `P` over `g⁻¹𝒪`.
* `Stacks.Sheaves.isLimitForkInverseImage`: **`g⁻¹H` is the equalizer of the row of `P` over
  `g⁻¹𝒪`.**
* `Stacks.Sheaves.inverseImageForkComparison_eq_lift`: the comparison morphism of
  `StacksFrontier.CategoryTheory.Sites.Topos.InverseImageSolutionComparison` is the canonical map
  of equalizers induced by the structure map `α`.
* `Stacks.Sheaves.exists_pullbackCoefficients`: the coefficients of the system over `g⁻¹𝒪`
  exist, with their defining equation — which discharges the `c₁` and `hc₁` hypotheses that the
  comparison was stated with.
* `Stacks.Sheaves.existsUnique_hom_comp_forkι`: **the comparison morphism, with no coefficient
  datum upstairs**: granted only the two equalizer presentations and the compatibility of the
  coefficients, there is a unique morphism `g⁻¹H ⟶ t.pt` carrying coordinates to coordinates.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Stacks.Sheaves.ToposPullback
open scoped CommRingObj Obj

universe w w' v u v' u'

namespace Stacks.Sheaves

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget CommRingCat.{w})] [K.HasSheafCompose (forget CommRingCat.{w'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K CommRingCat.{w'})

attribute [local instance] Stacks.sheafCommRingObj

variable {Γ : Type*} [CommRing Γ]
  (κ : Type) [Finite κ] {ν : Type} [Finite ν]
  {H : Sheaf K (Type w')} (ι : H ⟶ ∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf K O)
  (c : Γ →+* (𝟙_ (Sheaf K (Type w')) ⟶ Stacks.underlyingRingSheaf K O))
  (c₁ : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶
    Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O)))
  (hc₁ : ∀ r, c₁ r = Functor.LaxMonoidal.ε f.inverseImage ≫ f.inverseImage.map (c r))
  (P : ν → MvPolynomial κ Γ)

/-- **The coordinates carried by the inverse image of a sheaf with coordinates, with values in
`g⁻¹𝒪`.**  This is the inverse image of the coordinates downstairs, followed by the comparison
of the two `κ`-fold powers; it is the same morphism as
`Stacks.Sheaves.inverseImageCoordinates` before pushing along the structure map. -/
def inverseImagePullbackCoordinates :
    f.inverseImage.obj H ⟶ ∏ᶜ fun _ : κ =>
      Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O) :=
  f.inverseImage.map ι ≫
    piComparison f.inverseImage (fun _ : κ => Stacks.underlyingRingSheaf K O)

include hc₁ in
/-- **The pulled-back coordinates of `g⁻¹H` solve `P` over `g⁻¹𝒪`.**  The equation downstairs is
carried along by `g⁻¹` and then read in the sectionwise commutative ring object structure of the
inverse-image sheaf of commutative rings by
`Stacks.Sheaves.inverseImage_map_evalSystemHom_pullback`. -/
theorem inverseImagePullbackCoordinates_comp_evalSystemHom
    (hι : ι ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf K O) c κ P =
      ι ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf K O) κ ν) :
    inverseImagePullbackCoordinates f O κ ι ≫
        CommRingObj.evalSystemHom
          (Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O)) c₁ κ P =
      inverseImagePullbackCoordinates f O κ ι ≫
        CommRingObj.zeroSystemHom
          (Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O)) κ ν := by
  have hmap : f.inverseImage.map ι ≫ f.inverseImage.map
        (CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf K O) c κ P) =
      f.inverseImage.map ι ≫ f.inverseImage.map
        (CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf K O) κ ν) :=
    ((f.inverseImage.map_comp _ _).symm.trans (congrArg f.inverseImage.map hι)).trans
      (f.inverseImage.map_comp _ _)
  simp only [inverseImagePullbackCoordinates]
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (fun m => f.inverseImage.map ι ≫ m)
    (inverseImage_map_evalSystemHom_pullback f O κ c c₁ hc₁ P).symm) ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg
    (fun m => m ≫ piComparison f.inverseImage (fun _ : ν => Stacks.underlyingRingSheaf K O))
    hmap)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (fun m => f.inverseImage.map ι ≫ m)
    (inverseImage_map_zeroSystemHom_pullback f O κ ν)) ?_
  exact (Category.assoc _ _ _).symm

include hc₁ in
/-- **The inverse image of the equalizer presentation is the equalizer presentation over
`g⁻¹𝒪`.**

Let `H` be the equalizer of the row `∏ᵏ 𝒪 ⇉ ∏ᵛ 𝒪` of a polynomial system `P` over the structure
sheaf downstairs.  Then `g⁻¹H` is the equalizer of the row of the same system `P` over `g⁻¹𝒪`.

This is the use the source makes of exactness of `g⁻¹` in step (3) of the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6): only *left* exactness is used, and it
enters twice — once to make the mapped fork a fork
(`CategoryTheory.Limits.isLimitForkMapOfIsLimit`), and once to make the two power comparisons
isomorphisms, which is where finiteness of `κ` and `ν` is used. -/
def isLimitForkInverseImage
    (hι : ι ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf K O) c κ P =
      ι ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf K O) κ ν)
    (hs : IsLimit (Fork.ofι ι hι)) :
    IsLimit (Fork.ofι (inverseImagePullbackCoordinates f O κ ι)
      (inverseImagePullbackCoordinates_comp_evalSystemHom f O κ ι c c₁ hc₁ P hι)) := by
  haveI := f.preservesFiniteLimits
  exact Fork.isLimitOfIsos _ (isLimitForkMapOfIsLimit f.inverseImage hι hs) _
    (PreservesProduct.iso f.inverseImage (fun _ : κ => Stacks.underlyingRingSheaf K O))
    (PreservesProduct.iso f.inverseImage (fun _ : ν => Stacks.underlyingRingSheaf K O))
    (Iso.refl _)
    (inverseImage_map_evalSystemHom_pullback f O κ c c₁ hc₁ P).symm
    (inverseImage_map_zeroSystemHom_pullback f O κ ν).symm
    (Category.id_comp _)

section Comparison

variable {O' : Sheaf J CommRingCat.{w}}
  (α : pullbackCommRingSheaf J f.inverseImage O ⟶ O')
  (c' : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O'))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.HasSheafCompose (forget RingCat)] in
/-- **The coordinates of `g⁻¹H` over `𝒪'` are its coordinates over `g⁻¹𝒪` pushed along the
structure map.**  This is the definition of `Stacks.Sheaves.inverseImageCoordinates` reassociated
so that the inverse image of the equalizer presentation, `Stacks.Sheaves.isLimitForkInverseImage`,
is visible inside it. -/
theorem inverseImageCoordinates_eq :
    inverseImageCoordinates f O α κ ι =
      inverseImagePullbackCoordinates f O κ ι ≫
        Limits.Pi.map (fun _ : κ => PolynomialSystem.underlyingMap α) :=
  (Category.assoc _ _ _).symm

variable
  (hc' : ∀ r, c' r = c₁ r ≫ PolynomialSystem.underlyingMap α)
  {t : Limits.Fork (CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O') c' κ P)
    (CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O') κ ν)} (ht : IsLimit t)
  (hι : ι ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf K O) c κ P =
    ι ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf K O) κ ν)

include hc₁ hc' hι in
/-- **The comparison morphism is the canonical map of equalizers induced by the structure map.**

`Stacks.Sheaves.inverseImageForkComparison` was built from the universal property of the
equalizer upstairs applied to the coordinates of `g⁻¹H`.  Those coordinates are the coordinates
over `g⁻¹𝒪` — for which `g⁻¹H` is itself the equalizer, by
`Stacks.Sheaves.isLimitForkInverseImage` — pushed along `α`.  So the comparison is exactly the
map of equalizers that a map of the two rows induces, and it is the unique morphism whose
composite with the inclusion of the equalizer upstairs is the pushed-along inclusion of the
equalizer upstairs of `g⁻¹H`.

This is what locates the remaining content of step (4) of the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6): there is nothing left to construct,
and invertibility is a statement about the map `α` induces on the two sheaves of solutions. -/
theorem inverseImageForkComparison_eq_lift (m : f.inverseImage.obj H ⟶ t.pt)
    (hm : m ≫ Limits.Fork.ι t = inverseImagePullbackCoordinates f O κ ι ≫
      Limits.Pi.map (fun _ : κ => PolynomialSystem.underlyingMap α)) :
    m = inverseImageForkComparison f O α κ ι c c₁ hc₁ c' hc' P ht hι :=
  inverseImageForkComparison_unique f O α κ ι c c₁ hc₁ c' hc' P ht hι m
    (hm.trans (inverseImageCoordinates_eq f O κ ι α).symm)

end Comparison

/-! ### Discharging the coefficients upstairs

`Stacks.Sheaves.inverseImageForkComparison` and the statements around it take the coefficient
ring homomorphism `c₁` over `g⁻¹𝒪` as a *hypothesis*, together with the equation `hc₁` saying
what it is.  That was forced: the sectionwise commutative ring object structure on `g⁻¹𝒪` is
only propositionally equal to the one `g⁻¹` transports, so a `c₁` built from `c` by
`CategoryTheory.Functor.mapGlobalRingHom` has the *transported* structure's type, and a
transported copy of it would carry no usable defining equation.

It does, however, exist, and `Stacks.Sheaves.exists_pullbackCoefficients` produces it with its
equation — the equality of structures is rewritten in the *statement*, where it is a `Prop` and
the rewrite is unproblematic, instead of in a term.  With it the whole interface becomes free of
`c₁`: `Stacks.Sheaves.existsUnique_hom_comp_forkι` asks only for a compatibility between the
coefficients downstairs and the coefficients upstairs. -/

section Discharge

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The coefficients of the system over `g⁻¹𝒪` exist, with their defining equation.**  There
is a ring homomorphism from the coefficient ring to the global sections of `g⁻¹𝒪`, for the
*sectionwise* commutative ring object structure, whose value at `r` is the global section
`ε ≫ g⁻¹(c r)`.

The witness is `CategoryTheory.Functor.mapGlobalRingHom` composed with `c`, which is a ring
homomorphism for the *transported* structure; the two structures are equal by
`Stacks.Sheaves.ToposPullback.commRingObjObj_eq_sheafCommRingObj`, and because the conclusion is
a `Prop` that equality can simply be rewritten in it. -/
theorem exists_pullbackCoefficients :
    ∃ d : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶
        Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O)),
      ∀ r, d r = Functor.LaxMonoidal.ε f.inverseImage ≫ f.inverseImage.map (c r) := by
  rw [← commRingObjObj_eq_sheafCommRingObj J f.inverseImage O]
  exact ⟨(f.inverseImage.mapGlobalRingHom (Stacks.underlyingRingSheaf K O)).comp c,
    fun _ => rfl⟩

variable {O' : Sheaf J CommRingCat.{w}}
  (α : pullbackCommRingSheaf J f.inverseImage O ⟶ O')
  (c' : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O'))

/-- **The comparison morphism from the inverse image of a sheaf of solutions, with no coefficient
datum upstairs.**

Let the solutions of `P` over `𝒪'` be cut out by a limit fork `t`, let the coordinates of `H`
solve `P` over `𝒪` downstairs, and let the coefficients `c'` of the system over `𝒪'` be the
coefficients `c` downstairs carried along `g⁻¹` and then pushed along the structure map `α`.
Then there is a *unique* morphism `g⁻¹H ⟶ t.pt` carrying the coordinates of `g⁻¹H` to the
coordinates of the sheaf of solutions upstairs.

This is step (3) of the proof of [Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6) with
all of its data discharged: the comparison `g⁻¹h_V ⟶ h_{X ×_Y V}` exists and is pinned down by
what it does on coordinates, granted only the two equalizer presentations and the compatibility
of the coefficients, which is `Stacks.Sheaves.inverseImage_evalSystemHom_comp_fSharp` read on
global sections.  It is not asserted to be an isomorphism; see the module documentation. -/
theorem existsUnique_hom_comp_forkι
    (hc' : ∀ r, c' r = (Functor.LaxMonoidal.ε f.inverseImage ≫ f.inverseImage.map (c r)) ≫
      PolynomialSystem.underlyingMap α)
    {t : Limits.Fork (CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O') c' κ P)
      (CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O') κ ν)} (ht : IsLimit t)
    (hι : ι ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf K O) c κ P =
      ι ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf K O) κ ν) :
    ∃! m : f.inverseImage.obj H ⟶ t.pt,
      m ≫ Limits.Fork.ι t = inverseImageCoordinates f O α κ ι := by
  obtain ⟨d, hd⟩ := exists_pullbackCoefficients f O c
  have hd' : ∀ r, c' r = d r ≫ PolynomialSystem.underlyingMap α := fun r =>
    (hc' r).trans
      (congrArg (fun m => m ≫ PolynomialSystem.underlyingMap α) (hd r).symm)
  exact ⟨inverseImageForkComparison f O α κ ι c d hd c' hd' P ht hι,
    inverseImageForkComparison_comp_ι f O α κ ι c d hd c' hd' P ht hι,
    inverseImageForkComparison_unique f O α κ ι c d hd c' hd' P ht hι⟩

end Discharge

end Stacks.Sheaves

end
