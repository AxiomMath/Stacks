module

public import StacksFrontier.CategoryTheory.Sites.Topos.InverseImageCommRingObj
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiPolynomialEvaluation
public import StacksFrontier.CategoryTheory.Sites.Topos.RingSheafHomPolynomialEvaluation

/-!
# Polynomial rows pulled back along a morphism of ringed topoi and pushed along `g^♯`

Let `(g, g^♯) : (Sh(C), 𝒪') ⟶ (Sh(D), 𝒪)` be a morphism of ringed topoi, written here with the
structure map in its *inverse-image* form `g^♯ : g⁻¹𝒪 ⟶ 𝒪'` — the shape
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` has. Given a system of polynomials
`P₁, …, P_ν` in `κ` variables with coefficients in a ring `Γ`, read into the global sections of
`𝒪`, there are two things one can do to the row `∏ᵏ 𝒪 ⇉ ∏ᵛ 𝒪` that cuts out its solutions:

* apply `g⁻¹`, which is left exact and so preserves the two powers and the whole fork.  This is
  `Stacks.Sheaves.inverseImage_map_evalSystemHom`; it lands on `g⁻¹𝒪` with the commutative ring
  object structure that `g⁻¹` *transports*;
* push along `g^♯`, which is a morphism of the internal commutative ring objects.  This is
  `Stacks.Sheaves.PolynomialSystem.evalSystemHom_comp_piMap`; it starts from `g⁻¹𝒪` with the
  *sectionwise* ring object structure of the inverse-image sheaf of commutative rings.

The two ring object structures on `g⁻¹𝒪` are equal, by
`Stacks.Sheaves.ToposPullback.commRingObjObj_eq_sheafCommRingObj`, so the two steps compose.
The composite says that the row over `𝒪`, pulled back and pushed along `g^♯`, is the row of the
*same* system over `𝒪'`, its coefficients read into the global sections of `𝒪'` through `g^♯`.
The coefficient ring homomorphisms upstairs are hypotheses, together with the equations `hc₁`
and `hc'` that identify them.

## Main results

* `Stacks.Sheaves.inverseImage_map_evalSystemHom_pullback` and
  `Stacks.Sheaves.inverseImage_map_zeroSystemHom_pullback`: the two legs of the row, pulled back
  along `g⁻¹`, stated for the *sectionwise* commutative ring object of the inverse-image sheaf of
  commutative rings rather than the transported one.
* `Stacks.Sheaves.inverseImage_evalSystemHom_comp_fSharp` and
  `Stacks.Sheaves.inverseImage_zeroSystemHom_comp_fSharp`: the composite, which is the statement
  described above.

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

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The row of a polynomial system, pulled back along `g⁻¹`, read in the inverse-image sheaf of
commutative rings.**  This is `Stacks.Sheaves.inverseImage_map_evalSystemHom` with the
commutative ring object structure on `g⁻¹𝒪` taken to be the sectionwise one of
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf` rather than the one `g⁻¹` transports; the
two are equal by `Stacks.Sheaves.ToposPullback.commRingObjObj_eq_sheafCommRingObj`.

The coefficients upstairs are given as a ring homomorphism `c₁` for the sectionwise structure,
together with the equation `hc₁` identifying it with the image of `c` under `g⁻¹`. -/
theorem inverseImage_map_evalSystemHom_pullback (κ : Type) [Finite κ] {ν : Type} [Finite ν]
    (c : Γ →+* (𝟙_ (Sheaf K (Type w')) ⟶ Stacks.underlyingRingSheaf K O))
    (c₁ : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶
      Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O)))
    (hc₁ : ∀ r, c₁ r = Functor.LaxMonoidal.ε f.inverseImage ≫ f.inverseImage.map (c r))
    (P : ν → MvPolynomial κ Γ) :
    f.inverseImage.map (CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf K O) c κ P) ≫
        piComparison f.inverseImage (fun _ : ν => Stacks.underlyingRingSheaf K O) =
      piComparison f.inverseImage (fun _ : κ => Stacks.underlyingRingSheaf K O) ≫
        CommRingObj.evalSystemHom
          (Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O)) c₁ κ P := by
  revert c₁
  rw [← commRingObjObj_eq_sheafCommRingObj J f.inverseImage O]
  intro c₁ hc₁
  obtain rfl : c₁ = (f.inverseImage.mapGlobalRingHom (Stacks.underlyingRingSheaf K O)).comp c :=
    RingHom.ext hc₁
  exact inverseImage_map_evalSystemHom f O κ c P

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The zero row, pulled back along `g⁻¹`, read in the inverse-image sheaf of commutative
rings.**  The companion of `Stacks.Sheaves.inverseImage_map_evalSystemHom_pullback` for the other
leg of the equalizer presentation. -/
theorem inverseImage_map_zeroSystemHom_pullback (κ ν : Type) [Finite κ] [Finite ν] :
    f.inverseImage.map (CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf K O) κ ν) ≫
        piComparison f.inverseImage (fun _ : ν => Stacks.underlyingRingSheaf K O) =
      piComparison f.inverseImage (fun _ : κ => Stacks.underlyingRingSheaf K O) ≫
        CommRingObj.zeroSystemHom
          (Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O)) κ ν := by
  rw [← commRingObjObj_eq_sheafCommRingObj J f.inverseImage O]
  exact inverseImage_map_zeroSystemHom f O κ ν

variable {O' : Sheaf J CommRingCat.{w}}

/-- **The row of a polynomial system, pulled back along `g⁻¹` and pushed along `g^♯`, is the row
of the same system over the structure sheaf upstairs.**

Let `(g, g^♯)` be a morphism of ringed topoi with the structure map written in its inverse-image
form `α : g⁻¹𝒪 ⟶ 𝒪'`.  Applying `g⁻¹` to the arrow `∏ᵏ 𝒪 ⟶ ∏ᵛ 𝒪` of a polynomial system and
then pushing both powers along `α` gives the arrow of the *same* system over `𝒪'`, its
coefficients read into the global sections of `𝒪'` by composing `g⁻¹` with `α` — which is the
hypothesis `hc'`. -/
theorem inverseImage_evalSystemHom_comp_fSharp
    (α : pullbackCommRingSheaf J f.inverseImage O ⟶ O')
    (κ : Type) [Finite κ] {ν : Type} [Finite ν]
    (c : Γ →+* (𝟙_ (Sheaf K (Type w')) ⟶ Stacks.underlyingRingSheaf K O))
    (c₁ : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶
      Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O)))
    (hc₁ : ∀ r, c₁ r = Functor.LaxMonoidal.ε f.inverseImage ≫ f.inverseImage.map (c r))
    (c' : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O'))
    (hc' : ∀ r, c' r = c₁ r ≫ PolynomialSystem.underlyingMap α)
    (P : ν → MvPolynomial κ Γ) :
    f.inverseImage.map (CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf K O) c κ P) ≫
        piComparison f.inverseImage (fun _ : ν => Stacks.underlyingRingSheaf K O) ≫
        Limits.Pi.map (fun _ : ν => PolynomialSystem.underlyingMap α) =
      piComparison f.inverseImage (fun _ : κ => Stacks.underlyingRingSheaf K O) ≫
        Limits.Pi.map (fun _ : κ => PolynomialSystem.underlyingMap α) ≫
        CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O') c' κ P := by
  have hc : (PolynomialSystem.postcompRingHom α (𝟙_ (Sheaf J (Type w)))).comp c₁ = c' :=
    RingHom.ext fun r => (PolynomialSystem.postcompRingHom_apply α _ (c₁ r)).trans (hc' r).symm
  rw [← hc, reassoc_of% inverseImage_map_evalSystemHom_pullback f O κ c c₁ hc₁ P]
  exact (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (PolynomialSystem.evalSystemHom_comp_piMap α c₁ κ P))

/-- **The zero row, pulled back along `g⁻¹` and pushed along `g^♯`, is the zero row upstairs.**
The companion of `Stacks.Sheaves.inverseImage_evalSystemHom_comp_fSharp` for the other leg of the
equalizer presentation. -/
theorem inverseImage_zeroSystemHom_comp_fSharp
    (α : pullbackCommRingSheaf J f.inverseImage O ⟶ O') (κ ν : Type) [Finite κ] [Finite ν] :
    f.inverseImage.map (CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf K O) κ ν) ≫
        piComparison f.inverseImage (fun _ : ν => Stacks.underlyingRingSheaf K O) ≫
        Limits.Pi.map (fun _ : ν => PolynomialSystem.underlyingMap α) =
      piComparison f.inverseImage (fun _ : κ => Stacks.underlyingRingSheaf K O) ≫
        Limits.Pi.map (fun _ : κ => PolynomialSystem.underlyingMap α) ≫
        CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O') κ ν := by
  rw [reassoc_of% inverseImage_map_zeroSystemHom_pullback f O κ ν]
  exact (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (PolynomialSystem.zeroSystemHom_comp_piMap α κ ν))

end Stacks.Sheaves

end
