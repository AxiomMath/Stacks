module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Comparing the relative spectra of two isomorphic algebras on one base

Let `s` be a relative-spectrum situation and let `B` be a second quasi-coherent sheaf of
commutative algebras on the same base `s.base`, isomorphic to `s.algebra`. The two situations
then have isomorphic relative spectra, by the morphism corresponding, under the representing
bijection of [Stacks, Tag 01LV], to the pair consisting of the structure morphism of the second
relative spectrum and its universal algebra map precomposed with the given isomorphism.

## Main definitions

* `Stacks.RelativeSpec.algebraHomAsUnder`: a morphism of algebra sheaves, viewed as a morphism
  of the underlying presheaves under the structure presheaf of the base.
* `Stacks.RelativeSpec.relativeSpecFunctorMapOfAlgebraHom`: the contravariant action of a
  morphism of algebras on relative-spectrum functors [Stacks, Tag 01LR].
* `Stacks.RelativeSpec.relativeSpecFunctorIsoOfAlgebraIso`: the isomorphism of functors induced
  by an isomorphism of algebras.
* `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso`: the induced morphism of relative
  spectra.

## Main results

* `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso_homEquiv`: the universal element of the
  comparison.
* `Stacks.RelativeSpec.isIso_homEquiv_symm_of_representableBy`: the morphism between two
  representing objects induced by an isomorphism of the represented functors is an isomorphism.
* `Stacks.RelativeSpec.isIso_relativeSpectrumMapOfAlgebraIso`: the comparison is an isomorphism.
* `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso_toBase`: the comparison is a morphism
  over the base.
* `Stacks.RelativeSpec.isPullback_comp_of_isIso`: a Cartesian square stays Cartesian when its
  top-left corner is replaced along an isomorphism.

## Implementation notes

Equalities between sections of the algebra sheaf are not type-correct at `implicit`
transparency (`TopCat.Sheaf` is a semireducible definition for `CategoryTheory.Sheaf`), so `rw`
fails its motive check on them; such goals are discharged in term mode rather than by `rw` or
`simp`.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LR](https://stacks.math.columbia.edu/tag/01LR)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

universe u

namespace Stacks.RelativeSpec

/-- The relative-spectrum situation on the base of `s` with the quasi-coherent algebra `B` in
place of `s.algebra`. -/
public abbrev RelativeSpecSituation.withAlgebra (s : RelativeSpecSituation.{u})
    (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent) : RelativeSpecSituation.{u} :=
  { base := s.base, algebra := B, isQuasicoherent := hB }

/-! ### A morphism of algebra sheaves as a morphism under the structure sheaf -/

/-- A morphism `f : A ⟶ B` of algebra sheaves on `S`, viewed as a morphism in
`CategoryTheory.Under` of the structure presheaf of `S` between the underlying presheaves of `A`
and `B`. -/
public def algebraHomAsUnder {S : Scheme.{u}} {A B : AlgebraSheaf S} (f : A ⟶ B) :
    Under.mk A.hom.hom ⟶ Under.mk B.hom.hom :=
  Under.homMk f.right.hom (by
    change (A.hom ≫ f.right).hom = B.hom.hom
    exact congrArg (fun t => t.hom) f.w)

/-- `Stacks.RelativeSpec.algebraHomAsUnder` sends the identity to the identity. -/
@[simp]
public theorem algebraHomAsUnder_id {S : Scheme.{u}} (A : AlgebraSheaf S) :
    algebraHomAsUnder (𝟙 A) = 𝟙 (Under.mk A.hom.hom) :=
  rfl

/-- `Stacks.RelativeSpec.algebraHomAsUnder` preserves composition. -/
@[simp]
public theorem algebraHomAsUnder_comp {S : Scheme.{u}} {A B C : AlgebraSheaf S}
    (f : A ⟶ B) (g : B ⟶ C) :
    algebraHomAsUnder (f ≫ g) = algebraHomAsUnder f ≫ algebraHomAsUnder g :=
  rfl

/-- For an isomorphism `i : A ≅ B` of algebra sheaves, the images of `i.hom` and `i.inv` under
`Stacks.RelativeSpec.algebraHomAsUnder` compose to the identity of `A`. -/
@[simp]
public theorem algebraHomAsUnder_hom_inv_id {S : Scheme.{u}} {A B : AlgebraSheaf S}
    (i : A ≅ B) :
    algebraHomAsUnder i.hom ≫ algebraHomAsUnder i.inv = 𝟙 (Under.mk A.hom.hom) :=
  (algebraHomAsUnder_comp i.hom i.inv).symm.trans
    ((congrArg algebraHomAsUnder i.hom_inv_id).trans (algebraHomAsUnder_id A))

/-- For an isomorphism `i : A ≅ B` of algebra sheaves, the images of `i.inv` and `i.hom` under
`Stacks.RelativeSpec.algebraHomAsUnder` compose to the identity of `B`. -/
@[simp]
public theorem algebraHomAsUnder_inv_hom_id {S : Scheme.{u}} {A B : AlgebraSheaf S}
    (i : A ≅ B) :
    algebraHomAsUnder i.inv ≫ algebraHomAsUnder i.hom = 𝟙 (Under.mk B.hom.hom) :=
  algebraHomAsUnder_hom_inv_id i.symm

/-! ### The contravariant action on relative-spectrum functors -/

/-- The contravariant action of a morphism of algebras `ψ : s.algebra ⟶ B` on
relative-spectrum functors: a pair `(f, φ : B ⟶ f_* 𝒪_T)` over a test scheme `T` is sent to
`(f, ψ ≫ φ)`. -/
public def relativeSpecFunctorMapOfAlgebraHom (s : RelativeSpecSituation.{u})
    (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent) (ψ : s.algebra ⟶ B) :
    relativeSpecFunctor (s.withAlgebra B hB) ⟶ relativeSpecFunctor s where
  app T := ↾fun p : RelativeSpecPair (s.withAlgebra B hB) T.unop ↦
    ⟨p.1, algebraHomAsUnder ψ ≫ p.2⟩
  naturality _ _ _ := by
    ext p
    exact Sigma.ext rfl (heq_of_eq (Category.assoc _ _ _).symm)

/-- The isomorphism of relative-spectrum functors induced by an isomorphism of algebras on one
base, given in both directions by `Stacks.RelativeSpec.relativeSpecFunctorMapOfAlgebraHom`. -/
public def relativeSpecFunctorIsoOfAlgebraIso (s : RelativeSpecSituation.{u})
    (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent) (i : s.algebra ≅ B) :
    relativeSpecFunctor (s.withAlgebra B hB) ≅ relativeSpecFunctor s where
  hom := relativeSpecFunctorMapOfAlgebraHom s B hB i.hom
  inv := relativeSpecFunctorMapOfAlgebraHom (s.withAlgebra B hB) s.algebra s.isQuasicoherent i.inv
  hom_inv_id := by
    ext _ p
    exact Sigma.ext rfl (heq_of_eq ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ p.2) (algebraHomAsUnder_inv_hom_id i)).trans
        (Category.id_comp p.2))))
  inv_hom_id := by
    ext _ p
    exact Sigma.ext rfl (heq_of_eq ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ p.2) (algebraHomAsUnder_hom_inv_id i)).trans
        (Category.id_comp p.2))))

/-! ### The induced comparison of relative spectra -/

/-- If `F` is represented by `Y`, `F'` by `Y'` and `α : F' ≅ F`, then the morphism `Y' ⟶ Y`
corresponding to the image under `α` of the universal element of `Y'` is an isomorphism. -/
@[ega "0 8.1.8" "partial"]
public theorem isIso_homEquiv_symm_of_representableBy {C : Type*} [Category C]
    {F F' : Cᵒᵖ ⥤ Type _} {Y Y' : C} (R : F.RepresentableBy Y) (R' : F'.RepresentableBy Y')
    (α : F' ≅ F) :
    IsIso (R.homEquiv.symm (α.hom.app (op Y') (R'.homEquiv (𝟙 Y')))) := by
  change IsIso ((R'.ofIso α).uniqueUpToIso R).hom
  infer_instance

/-- The morphism of relative spectra induced by an isomorphism of algebras on one base: the
morphism whose universal element is the structure morphism of the second relative spectrum
together with the second universal algebra map precomposed with the isomorphism. -/
public def relativeSpectrumMapOfAlgebraIso (s : RelativeSpecSituation.{u})
    (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent) (i : s.algebra ≅ B) :
    (gluedSpectrum (s.withAlgebra B hB)).scheme ⟶ (gluedSpectrum s).scheme :=
  (relativeSpecRepresentableBy s).homEquiv.symm
    ⟨(gluedSpectrum (s.withAlgebra B hB)).toBase,
      algebraHomAsUnder i.hom ≫
        (universalAlgebraMap (s.withAlgebra B hB))⟩

/-- Under the representing bijection, `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso`
corresponds to the structure morphism of the second relative spectrum paired with the second
universal algebra map precomposed with the isomorphism. -/
public theorem relativeSpectrumMapOfAlgebraIso_homEquiv (s : RelativeSpecSituation.{u})
    (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent) (i : s.algebra ≅ B) :
    (relativeSpecRepresentableBy s).homEquiv
        (relativeSpectrumMapOfAlgebraIso s B hB i) =
      ⟨(gluedSpectrum (s.withAlgebra B hB)).toBase,
        algebraHomAsUnder i.hom ≫
          (universalAlgebraMap (s.withAlgebra B hB))⟩ :=
  (relativeSpecRepresentableBy s).homEquiv.apply_symm_apply _

/-- The comparison of relative spectra along an isomorphism of algebras is an isomorphism. -/
public theorem isIso_relativeSpectrumMapOfAlgebraIso (s : RelativeSpecSituation.{u})
    (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent) (i : s.algebra ≅ B) :
    IsIso (relativeSpectrumMapOfAlgebraIso s B hB i) := by
  have hid : (relativeSpecRepresentableBy (s.withAlgebra B hB)).homEquiv (𝟙 _) =
      universalRelativeSpecPair (s.withAlgebra B hB) :=
    congrArg (Sigma.mk _) rfl
  have h : (relativeSpecFunctorIsoOfAlgebraIso s B hB i).hom.app
        (op (gluedSpectrum (s.withAlgebra B hB)).scheme)
        ((relativeSpecRepresentableBy (s.withAlgebra B hB)).homEquiv (𝟙 _)) =
      ⟨(gluedSpectrum (s.withAlgebra B hB)).toBase,
        algebraHomAsUnder i.hom ≫
          (universalAlgebraMap (s.withAlgebra B hB))⟩ :=
    congrArg
      ((relativeSpecFunctorIsoOfAlgebraIso s B hB i).hom.app
        (op (gluedSpectrum (s.withAlgebra B hB)).scheme))
      hid
  have key := isIso_homEquiv_symm_of_representableBy
    (relativeSpecRepresentableBy s)
    (relativeSpecRepresentableBy (s.withAlgebra B hB))
    (relativeSpecFunctorIsoOfAlgebraIso s B hB i)
  rwa [h] at key

/-- The comparison of relative spectra along an isomorphism of algebras is a morphism over the
base. -/
public theorem relativeSpectrumMapOfAlgebraIso_toBase (s : RelativeSpecSituation.{u})
    (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent) (i : s.algebra ≅ B) :
    relativeSpectrumMapOfAlgebraIso s B hB i ≫ (gluedSpectrum s).toBase =
      (gluedSpectrum (s.withAlgebra B hB)).toBase :=
  (relativeSpecRepresentableBy_homEquiv_fst s
      (relativeSpectrumMapOfAlgebraIso s B hB i)).symm.trans
    (congrArg Sigma.fst (relativeSpectrumMapOfAlgebraIso_homEquiv s B hB i))

/-! ### Transporting a Cartesian square along such a comparison -/

/-- A Cartesian square stays Cartesian when its top-left corner is replaced along an
isomorphism `k : P' ⟶ P` compatible with the first leg. -/
public theorem isPullback_comp_of_isIso {C : Type*} [Category C] {P P' Y Z T : C}
    {fst : P ⟶ Y} {snd : P ⟶ T} {g : Y ⟶ Z} {h : T ⟶ Z}
    (sq : IsPullback fst snd g h) (k : P' ⟶ P) [IsIso k] {fst' : P' ⟶ Y}
    (hk : k ≫ fst = fst') : IsPullback fst' (k ≫ snd) g h :=
  sq.of_iso' (asIso k) (Iso.refl Y) (Iso.refl T) (Iso.refl Z)
    (hk.trans (Category.comp_id fst').symm)
    (Category.comp_id (k ≫ snd)).symm
    ((Category.id_comp g).trans (Category.comp_id g).symm)
    ((Category.id_comp h).trans (Category.comp_id h).symm)

end Stacks.RelativeSpec

end
