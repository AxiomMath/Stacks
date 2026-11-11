module

public import StacksFrontier.RingTheory.NaiveCotangent.ExtensionQuasiIso
public import StacksFrontier.RingTheory.NaiveCotangent.H1

/-!
# The naive cotangent complex of a surjection

Let `A → B` be a surjective ring map with kernel `I := RingHom.ker (algebraMap A B)`. The naive
cotangent complex `NL_{B/A}` is homotopy equivalent to the two-term complex `(I/I² → 0)` with
`I/I²` in degree `1` (Stacks 07BP). The consequence `H₁(L_{B/A}) = I/I²` is
`h1Cotangent_equiv_cotangent_of_surjective`.

## Main definitions

* `NaiveCotangent.conormalTwoTerm`: the two-term complex `(I/I² → 0)` of `B`-modules.
* `NaiveCotangent.nlToConormalOfSurjective`: the chain map `NL_{B/A} ⟶ (I/I² → 0)` induced by
  the presentation `A → B` of `B` over `A`.

## Main results

* `NaiveCotangent.nlToConormalOfSurjective_isHomotopyEquiv`: the chain map
  `NL_{B/A} ⟶ (I/I² → 0)` is a homotopy equivalence (Stacks 07BP).

## References

* [Stacks Project, Tag 07BP](https://stacks.math.columbia.edu/tag/07BP)
-/

@[expose] public section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]


namespace NaiveCotangent

open Algebra

/-- The extension `A → B` of `B` over `A` for a surjective `algebraMap A B`, with ring `A` and
kernel `I := RingHom.ker (algebraMap A B)`: `Algebra.Extension.ofSurjective` at `Algebra.ofId A B`.
-/
noncomputable abbrev ofSurjectiveExtension (h : Function.Surjective (algebraMap A B)) :
    Extension A B :=
  Extension.ofSurjective (Algebra.ofId A B) fun b => (h b).imp fun _ ha => ha

/-- For a surjective `algebraMap A B`, the cotangent space `Ω_{A/A} ⊗_A B` of the extension
`A → B` is zero. -/
theorem subsingleton_cotangentSpace_ofSurjective (h : Function.Surjective (algebraMap A B)) :
    Subsingleton (ofSurjectiveExtension h).CotangentSpace := by
  have : Subsingleton (Ω[(ofSurjectiveExtension h).Ring⁄A]) :=
    KaehlerDifferential.subsingleton_of_surjective A A Function.surjective_id
  unfold Algebra.Extension.CotangentSpace
  infer_instance

/-- The two-term complex `(I/I² → 0)` of `B`-modules for a surjective `algebraMap A B` with kernel
`I := RingHom.ker (algebraMap A B)`: the conormal module `I/I² = I.Cotangent` in degree `1`, with
`B = A/I` acting through any lift to `A`, the zero module in degree `0`, and the zero
differential. -/
noncomputable def conormalTwoTerm (h : Function.Surjective (algebraMap A B)) : TwoTerm B where
  X₁ := (RingHom.ker (algebraMap A B)).Cotangent
  X₀ := PUnit.{1}
  inst₁ := inferInstanceAs (AddCommGroup (ofSurjectiveExtension h).Cotangent)
  mod₁ := inferInstanceAs (Module B (ofSurjectiveExtension h).Cotangent)
  d := 0

/-- The identification of the naive cotangent complex of the extension `A → B` with
`(I/I² → 0)`: the identity in degree `1` and zero in degree `0`. -/
noncomputable def nlOfSurjectiveToConormal (h : Function.Surjective (algebraMap A B)) :
    ChainMap (nlOfExtension (ofSurjectiveExtension h)) (conormalTwoTerm h)
    where
  f₁ := LinearMap.id
  f₀ := 0
  comm := LinearMap.ext fun _ => rfl

/-- The inverse of `nlOfSurjectiveToConormal`: the identity in degree `1` and zero in
degree `0`. -/
noncomputable def conormalToNlOfSurjective (h : Function.Surjective (algebraMap A B)) :
    ChainMap (conormalTwoTerm h) (nlOfExtension (ofSurjectiveExtension h))
    where
  f₁ := LinearMap.id
  f₀ := 0
  comm := by
    have : Subsingleton (nlOfExtension (ofSurjectiveExtension h)).X₀ :=
      subsingleton_cotangentSpace_ofSurjective h
    exact LinearMap.ext fun _ => Subsingleton.elim _ _

/-- The chain map `NL_{B/A} ⟶ (I/I² → 0)` for a surjective `algebraMap A B` with kernel `I`:
the map of naive cotangent complexes induced by the canonical morphism from the presentation
`A[B] → B` to the presentation `A → B`, followed by the identification of the naive cotangent
complex of `A → B` with `(I/I² → 0)`. -/
noncomputable def nlToConormalOfSurjective (h : Function.Surjective (algebraMap A B)) :
    ChainMap (NL (Generators.self A B)) (conormalTwoTerm h) :=
  (nlOfSurjectiveToConormal h).comp
    (nlExtensionMap (Extension.defaultHom A B (ofSurjectiveExtension h)))

/-- The morphism of extensions from the presentation `A → B` to the presentation `A[B] → B`,
given by the structure map `A → A[B]`. -/
noncomputable def ofSurjectiveHomSelf (h : Function.Surjective (algebraMap A B)) :
    (ofSurjectiveExtension h).Hom (Generators.self A B).toExtension :=
  Extension.Hom.ofAlgHom (Algebra.ofId A (MvPolynomial B A))
    (Subsingleton.elim (α := A →ₐ[A] B) _ _)

/-- **Stacks 07BP.** Let `A → B` be a surjective ring map with kernel `I`. Then the naive
cotangent complex `NL_{B/A}` is homotopy equivalent to the chain complex `(I/I² → 0)` with
`I/I²` in degree `1`, via `nlToConormalOfSurjective`. -/
@[stacks 07BP "the homotopy equivalence `NL_{B/A} ≃ (I/I^2 → 0)`; the consequence
`H_1(L_{B/A}) = I/I^2` is `h1Cotangent_equiv_cotangent_of_surjective`"]
theorem nlToConormalOfSurjective_isHomotopyEquiv (h : Function.Surjective (algebraMap A B)) :
    IsHomotopyEquiv (nlToConormalOfSurjective h) := by
  have : Subsingleton (nlOfExtension (ofSurjectiveExtension h)).X₀ :=
    subsingleton_cotangentSpace_ofSurjective h
  have : Subsingleton (conormalTwoTerm h).X₀ := inferInstanceAs (Subsingleton PUnit.{1})
  set d := Extension.defaultHom A B (ofSurjectiveExtension h)
  set g := ofSurjectiveHomSelf h
  refine ⟨(nlExtensionMap g).comp (conormalToNlOfSurjective h), ?_, ⟨0, ?_, ?_⟩⟩
  · have key : ((nlExtensionMap g).comp (conormalToNlOfSurjective h)).comp
        (nlToConormalOfSurjective h) = nlExtensionMap (g.comp d) := by
      refine ChainMap.ext (LinearMap.ext fun x => ?_) (LinearMap.ext fun x => ?_)
      · exact (congr($(Extension.Cotangent.map_comp _ d g) x)).symm
      · have hx : (conormalToNlOfSurjective h).f₀ ((nlOfSurjectiveToConormal h).f₀
            (Extension.CotangentSpace.map d x)) = Extension.CotangentSpace.map d x :=
          Subsingleton.elim _ _
        exact (congrArg (Extension.CotangentSpace.map g) hx).trans
          (Extension.CotangentSpace.map_comp_apply d g x).symm
    have hg := nlExtensionMap_homotopic (g.comp d) (Extension.Hom.id _)
    rw [nlExtensionMap_id] at hg
    exact (congrArg (fun F => Homotopic F (ChainMap.id (NL (Generators.self A B)))) key).mpr hg
  · have hid : ∀ y : (ofSurjectiveExtension h).Cotangent,
        Extension.Cotangent.map d (Extension.Cotangent.map g y) = y := by
      intro y
      obtain ⟨k, hk, -⟩ := nlExtensionMap_homotopic (d.comp g)
        (Extension.Hom.id (ofSurjectiveExtension h))
      have hy : Extension.Cotangent.map (d.comp g) y -
          Extension.Cotangent.map (Extension.Hom.id (ofSurjectiveExtension h)) y
          = k ((nlOfExtension (ofSurjectiveExtension h)).d y) := congr($hk y)
      have h0 : (nlOfExtension (ofSurjectiveExtension h)).d y = 0 := Subsingleton.elim _ _
      have hk0 : k ((nlOfExtension (ofSurjectiveExtension h)).d y) = 0 := by
        rw [h0, map_zero]
      have h2 : Extension.Cotangent.map (d.comp g) y =
          Extension.Cotangent.map (Extension.Hom.id (ofSurjectiveExtension h)) y :=
        sub_eq_zero.mp (hy.trans hk0)
      exact (congr($(Extension.Cotangent.map_comp _ g d) y)).symm.trans
        (h2.trans (LinearMap.congr_fun Extension.Cotangent.map_id y))
    exact LinearMap.ext fun x => (sub_eq_zero.mpr (hid x) :)
  · exact LinearMap.ext fun _ => Subsingleton.elim _ _

end NaiveCotangent

end
