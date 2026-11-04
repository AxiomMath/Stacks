module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSetsToposInverseImage

/-!
# The sheaf of closed degree-`i` local sections of a right differential graded module

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` be a sheaf of differential graded
`R`-algebras and let `Q` be a right differential graded `A`-module. Its *closed degree-`i` local
sections* over `U` are the degree-`i` sections killed by the differential `d^i`. They form a
sheaf of sets: the differential and the zero morphism are two morphisms of sheaves of sets
between the underlying sheaves of `Q^i` and `Q^{i + 1}`, and the sections on which two such
morphisms agree form a sheaf, which is `Stacks.eqFiber` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSetsToposInverseImage.lean`.

This is the target of the universal property of a free differential graded module in the shape
the base change of Tag 0FSG needs: a homomorphism `A[S] ⟶ Q` is exactly a family of morphisms of
sheaves of sets from the degree-`i` sections of `S` to the closed degree-`i` sections of `Q`, one
for each `i`. The grading side of that statement is `Stacks.degreeFiberSheaf`, and both sides are
sheaves of sets, which is what lets the adjunction `f⁻¹ ⊣ f_*` be applied to it degree by degree.

## Main definitions

* `SheafOfModules.toSetSheaf` is the underlying sheaf of sets of a sheaf of modules, as a
  functor.
* `SheafOfModules.DifferentialGradedModule.closedSection` and `closedSectionSheaf`: **the sheaf
  of closed degree-`i` local sections of a right differential graded module.**
* `SheafOfModules.DifferentialGradedModule.closedSectionMap` is its functoriality in the module,
  and `closedSectionFunctor` the resulting functor.
* `SheafOfModules.DifferentialGradedModule.closedSectionSheafTransportIso`: **the closed
  degree-`i` sections transport along a functor of sheaves of sets preserving the equalizer of
  the differential against zero**, with
  `closedSectionSheafTransportIso_hom_comp_ι` pinning the comparison down by its compatibility
  with the two inclusions.

## Main results

* `SheafOfModules.DifferentialGradedModule.closedSectionSheafIso`: the sheaf of closed
  degree-`i` sections is the equalizer of the differential and zero, taken in sheaves of sets.
  This is the form left exactness of a functor applies to.

The equalizer-preservation hypothesis of `closedSectionSheafTransportIso` is a hypothesis and
not an instance derived here. A right adjoint satisfies it, which is what makes the direct image
an instance; the *pullback* of sheaves of modules along a morphism of ringed topoi does not
satisfy it in general, and nothing below claims it does.

## Implementation notes

No `HasSheafify` and no sheafification hypothesis is carried: `Stacks.eqFiber` needs none, and
the only instance below is `J.HasSheafCompose (forget AddCommGrpCat.{m})`, which is what makes
the underlying sheaf of sets of a sheaf of modules exist at all. It is an instance hypothesis
letting the statements be written, not an assumed result.

The closedness condition is stated as `d x = 0` on sections rather than as equality with the
image of the zero morphism of sheaves of modules; the two are definitionally equal, and the
`rfl`-level lemmas `closedSection_obj` and `closedSectionSheaf_obj` record it, so a consumer may
build a closed section by an anonymous constructor.

Everything is stated for an arbitrary sheaf of rings on an arbitrary site, with the universes of
the site, of the sheaf of rings, of the homogeneous pieces of the algebra and of the module
sections independent, as in the neighbouring differential graded files.

## References

* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t a m v u t' a' m' v₁ u₁

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The underlying sheaf of sets of a sheaf of modules, as a functor. -/
noncomputable abbrev toSetSheaf (R : Sheaf J RingCat.{t}) :
    SheafOfModules.{m} R ⥤ Sheaf J (Type m) :=
  SheafOfModules.toSheaf R ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{m})

variable {R : Sheaf J RingCat.{t}}

/-- The underlying sheaf of sets functor acts on morphisms by the underlying map on sections. -/
theorem toSetSheaf_map_app {M N : SheafOfModules.{m} R} (g : M ⟶ N) (U : Cᵒᵖ)
    (x : ((toSetSheaf R).obj M).obj.obj U) :
    ((toSetSheaf R).map g).hom.app U x = g.val.app U x :=
  rfl

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The differential of a right differential graded module, read as a morphism of the underlying
sheaves of sets. -/
noncomputable abbrev dSetMap (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    (toSetSheaf R).obj (Q.complex.X i) ⟶ (toSetSheaf R).obj (Q.complex.X (i + 1)) :=
  (toSetSheaf R).map (Q.complex.d i (i + 1))

/-- The zero morphism between two homogeneous pieces, read as a morphism of the underlying
sheaves of sets. -/
noncomputable abbrev zeroSetMap (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    (toSetSheaf R).obj (Q.complex.X i) ⟶ (toSetSheaf R).obj (Q.complex.X (i + 1)) :=
  (toSetSheaf R).map 0

/-- **The presheaf of closed degree-`i` local sections of a right differential graded module**:
the sections of degree `i` killed by the differential. -/
noncomputable def closedSection (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    Cᵒᵖ ⥤ Type m :=
  Stacks.eqFiber (dSetMap Q i) (zeroSetMap Q i)

/-- The sections of the sheaf of closed degree-`i` sections are the degree-`i` sections killed
by the differential. -/
theorem closedSection_obj (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) (U : Cᵒᵖ) :
    (closedSection Q i).obj U =
      { x : (Q.complex.X i).val.obj U // (Q.complex.d i (i + 1)).val.app U x = 0 } :=
  rfl

/-- Restriction of a closed section is restriction of the underlying section. -/
theorem closedSection_map_val (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) {U V : Cᵒᵖ}
    (r : U ⟶ V) (x : (closedSection Q i).obj U) :
    ((closedSection Q i).map r x).1 = (Q.complex.X i).val.map r x.1 :=
  rfl

/-- The sheaf of closed degree-`i` local sections is a sheaf. -/
theorem closedSection_isSheaf (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    Presheaf.IsSheaf J (closedSection Q i) :=
  Stacks.eqFiber_isSheaf (dSetMap Q i) (zeroSetMap Q i)

/-- **The sheaf of closed degree-`i` local sections of a right differential graded module.** -/
noncomputable abbrev closedSectionSheaf (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    Sheaf J (Type m) :=
  Stacks.eqFiberSheaf (dSetMap Q i) (zeroSetMap Q i)

/-- The underlying presheaf of the sheaf of closed degree-`i` local sections. -/
theorem closedSectionSheaf_obj (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    (closedSectionSheaf Q i).obj = closedSection Q i :=
  rfl

/-- The sheaf of closed degree-`i` local sections is the equalizer of the differential and zero,
taken in the category of sheaves of sets. -/
noncomputable def closedSectionSheafIso (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    closedSectionSheaf Q i ≅ equalizer (dSetMap Q i) (zeroSetMap Q i) :=
  Stacks.eqFiberSheafIso (dSetMap Q i) (zeroSetMap Q i)

/-- The inclusion of the closed degree-`i` sections into the degree-`i` sections. -/
noncomputable abbrev closedSectionι (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    closedSectionSheaf Q i ⟶ (toSetSheaf R).obj (Q.complex.X i) :=
  Stacks.eqFiberι (dSetMap Q i) (zeroSetMap Q i)

/-- The inclusion of the closed sections sends a closed section to its underlying section. -/
@[simp]
theorem closedSectionι_app (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) (U : Cᵒᵖ)
    (x : (closedSection Q i).obj U) : (closedSectionι Q i).hom.app U x = x.1 :=
  rfl

/-- **The sheaf of closed degree-`i` sections is functorial in the module**: a morphism of right
differential graded modules commutes with the differentials, so it carries a closed section to a
closed section. -/
noncomputable def closedSectionMap {Q Q' : DifferentialGradedModule.{t, a, m} A} (k : Q ⟶ Q')
    (i : ℤ) : closedSectionSheaf Q i ⟶ closedSectionSheaf Q' i :=
  ⟨{ app U := ↾fun x =>
        ⟨(k.toHomologicalComplex.f i).val.app U x.1, by
          refine (homSections_congr (k.toHomologicalComplex.comm i (i + 1)) U x.1).trans ?_
          exact Eq.trans
            (congrArg (fun z => (k.toHomologicalComplex.f (i + 1)).val.app U z) x.2)
            (map_zero ((k.toHomologicalComplex.f (i + 1)).val.app U).hom)⟩
     naturality {U V} r := by
       ext x
       exact Subtype.ext
         (PresheafOfModules.naturality_apply (k.toHomologicalComplex.f i).val r x.1) }⟩

/-- The underlying section of the image of a closed section under `closedSectionMap k i` is the
image of its underlying section under the degree-`i` component of `k`. -/
@[simp]
theorem closedSectionMap_app {Q Q' : DifferentialGradedModule.{t, a, m} A} (k : Q ⟶ Q') (i : ℤ)
    (U : Cᵒᵖ) (x : (closedSection Q i).obj U) :
    ((closedSectionMap k i).hom.app U x).1 = (k.toHomologicalComplex.f i).val.app U x.1 :=
  rfl

/-- **The functoriality of the closed sections is compatible with the two inclusions.** -/
@[simp]
theorem closedSectionMap_comp_ι {Q Q' : DifferentialGradedModule.{t, a, m} A} (k : Q ⟶ Q')
    (i : ℤ) :
    closedSectionMap k i ≫ closedSectionι Q' i =
      closedSectionι Q i ≫ (toSetSheaf R).map (k.toHomologicalComplex.f i) :=
  rfl

/-- The identity morphism induces the identity on closed sections. -/
@[simp]
theorem closedSectionMap_id (Q : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    closedSectionMap (𝟙 Q) i = 𝟙 (closedSectionSheaf Q i) :=
  rfl

/-- The morphism induced on closed sections by a composite is the composite of the induced
morphisms. -/
@[simp]
theorem closedSectionMap_comp {Q Q' Q'' : DifferentialGradedModule.{t, a, m} A} (k : Q ⟶ Q')
    (k' : Q' ⟶ Q'') (i : ℤ) :
    closedSectionMap (k ≫ k') i = closedSectionMap k i ≫ closedSectionMap k' i :=
  rfl

/-! ### Transporting the closed sections along a functor preserving equalizers -/

section Transport

variable {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D} {R' : Sheaf K RingCat.{t'}}
  {A' : DifferentialGradedAlgebra.{t', a'} R'}

/-- **The closed degree-`i` sections transport along a functor of sheaves of sets which
preserves the relevant equalizer and is compatible with the two differentials.** Right adjoints
preserve equalizers and an additive functor sends zero to zero, so this is what applies to the
direct image; the hypotheses `hd` and `hz` are the two intertwining squares.

This does **not** assert that the comparison exists for a functor which is merely a left adjoint:
the equalizer-preservation instance is a hypothesis, and in particular the pullback of sheaves of
modules along a morphism of ringed topoi does not satisfy it in general. -/
noncomputable def closedSectionSheafTransportIso
    (Φ : Sheaf J (Type m) ⥤ Sheaf K (Type m'))
    (Q : DifferentialGradedModule.{t, a, m} A) (Q' : DifferentialGradedModule.{t', a', m'} A')
    (i : ℤ)
    (e : Φ.obj ((toSetSheaf R).obj (Q.complex.X i)) ≅ (toSetSheaf R').obj (Q'.complex.X i))
    (e' : Φ.obj ((toSetSheaf R).obj (Q.complex.X (i + 1))) ≅
      (toSetSheaf R').obj (Q'.complex.X (i + 1)))
    (hd : Φ.map (dSetMap Q i) ≫ e'.hom = e.hom ≫ dSetMap Q' i)
    (hz : Φ.map (zeroSetMap Q i) ≫ e'.hom = e.hom ≫ zeroSetMap Q' i)
    [Limits.PreservesLimit (parallelPair (dSetMap Q i) (zeroSetMap Q i)) Φ] :
    Φ.obj (closedSectionSheaf Q i) ≅ closedSectionSheaf Q' i :=
  Stacks.eqFiberSheafPreservesIso Φ (dSetMap Q i) (zeroSetMap Q i) ≪≫
    Stacks.eqFiberSheafCongrIso e e' hd hz

/-- **The transport of the closed sections is the comparison compatible with the two
inclusions.** With `Stacks.mono_eqFiberι` this determines it, and it is what every naturality
square for it reduces to. -/
theorem closedSectionSheafTransportIso_hom_comp_ι
    (Φ : Sheaf J (Type m) ⥤ Sheaf K (Type m'))
    (Q : DifferentialGradedModule.{t, a, m} A) (Q' : DifferentialGradedModule.{t', a', m'} A')
    (i : ℤ)
    (e : Φ.obj ((toSetSheaf R).obj (Q.complex.X i)) ≅ (toSetSheaf R').obj (Q'.complex.X i))
    (e' : Φ.obj ((toSetSheaf R).obj (Q.complex.X (i + 1))) ≅
      (toSetSheaf R').obj (Q'.complex.X (i + 1)))
    (hd : Φ.map (dSetMap Q i) ≫ e'.hom = e.hom ≫ dSetMap Q' i)
    (hz : Φ.map (zeroSetMap Q i) ≫ e'.hom = e.hom ≫ zeroSetMap Q' i)
    [Limits.PreservesLimit (parallelPair (dSetMap Q i) (zeroSetMap Q i)) Φ] :
    (closedSectionSheafTransportIso Φ Q Q' i e e' hd hz).hom ≫ closedSectionι Q' i =
      Φ.map (closedSectionι Q i) ≫ e.hom := by
  rw [closedSectionSheafTransportIso, Iso.trans_hom, Category.assoc,
    Stacks.eqFiberSheafCongrIso_hom_comp_ι, ← Category.assoc,
    Stacks.eqFiberSheafPreservesIso_hom_comp_ι]

end Transport

/-- The sheaf of closed degree-`i` local sections, as a functor of the right differential graded
module. -/
noncomputable def closedSectionFunctor (A : DifferentialGradedAlgebra.{t, a} R) (i : ℤ) :
    DifferentialGradedModule.{t, a, m} A ⥤ Sheaf J (Type m) where
  obj Q := closedSectionSheaf Q i
  map k := closedSectionMap k i
  map_id Q := closedSectionMap_id Q i
  map_comp k k' := closedSectionMap_comp k k' i

end DifferentialGradedModule

end SheafOfModules

end
