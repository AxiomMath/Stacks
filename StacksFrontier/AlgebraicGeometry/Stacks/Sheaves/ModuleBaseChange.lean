module

public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import Mathlib.CategoryTheory.Limits.Final.Type
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality

/-!
# Base change for direct images of sheaves of modules along a Guitart exact square

Let
```
  𝒵 --- a ---> 𝒳
  |            |
  b            f
  v            v
  𝒴' -- g ---> 𝒴
```
be a square of 1-morphisms of categories fibred in groupoids over the big fppf category of `S`,
commuting up to a 2-morphism `w : a ⋙ f ⟶ b ⋙ g` which is vertical (it lies over identities of
the base). If the square is Guitart exact, the base change map `g⁻¹ f_* ℱ ⟶ b_* a⁻¹ ℱ` of
sheaves of modules over the structure sheaves of Stacks 06TV is an isomorphism, naturally in `ℱ`.

## Main definitions

* `AlgebraicGeometry.Stack.sectionsBaseChange`: the base change map on compatible sections, the
  model of the direct image of Stacks 06WD.
* `AlgebraicGeometry.Stack.moduleSectionsBaseChangeIso`: the base change isomorphism
  `f_* ⋙ g⁻¹ ≅ a⁻¹ ⋙ b_*` on the compatible-sections models of presheaves of modules.

## Implementation notes

The direct image of presheaves of modules of Stacks 06WD is the module of compatible families of
sections over the comma category of the 1-morphism, and on such families the base change map is
restriction along the comparison functor of comma categories that Guitart exactness of the square
makes initial (`CategoryTheory.TwoSquare.structuredArrowDownwards`). So the map is linear by
construction, because it only ever evaluates a family at one of its own indices, and bijective by
`CategoryTheory.Functor.bijective_sectionsPrecomp`. No Kan extension is compared with another.

The only input about scalars is that the 2-cell of the square acts on the structure rings by
identities (`hRw`), which is what verticality of the 2-cell gives for the structure sheaf of a
category fibred in groupoids: that sheaf is the structure sheaf of the base composed with the
structure functor.

## References

* [Stacks Project, Tag 075B](https://stacks.math.columbia.edu/tag/075B)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u vP wP vX wX vY' wY' vY wY m

/-! ### Compatible sections as sections of a functor -/

section CompatibleSections

variable {C : Type vX} [Category.{wX} C] {D : Type vY} [Category.{wY} D] (L : C ⥤ D)
  (F : C ⥤ AddCommGrpCat.{m}) (y : D)

/-- A compatible family of sections over the comma category `y ↓ L` is a section of the functor
`y ↓ L ⥤ Type` reading off `F` at the target. -/
def compatibleSectionsToSections (s : compatibleSections L F y) :
    (StructuredArrow.proj y L ⋙ F ⋙ forget AddCommGrpCat).sections :=
  ⟨fun j => s.val j.right j.hom, fun {j j'} φ => by
    change F.map φ.right (s.val j.right j.hom) = s.val j'.right j'.hom
    rw [s.property j.right j'.right φ.right j.hom, StructuredArrow.w φ]⟩

/-- A section of the functor `y ↓ L ⥤ Type` reading off `F` is a compatible family. -/
def sectionsToCompatibleSections
    (σ : (StructuredArrow.proj y L ⋙ F ⋙ forget AddCommGrpCat).sections) :
    compatibleSections L F y :=
  ⟨fun _ h => σ.val (StructuredArrow.mk h), fun _ _ a h =>
    σ.property (StructuredArrow.homMk a rfl : StructuredArrow.mk h ⟶ StructuredArrow.mk
      (h ≫ L.map a))⟩

/-- `sectionsToCompatibleSections` is a left inverse of `compatibleSectionsToSections`. -/
lemma sectionsToCompatibleSections_toSections (s : compatibleSections L F y) :
    sectionsToCompatibleSections L F y (compatibleSectionsToSections L F y s) = s := rfl

/-- The map `compatibleSectionsToSections` from compatible families to sections is injective. -/
lemma compatibleSectionsToSections_injective :
    Function.Injective (compatibleSectionsToSections L F y) :=
  Function.LeftInverse.injective (sectionsToCompatibleSections_toSections L F y)

end CompatibleSections

/-! ### The base change map on compatible sections -/

section SectionsBaseChange

variable {𝒵 : Type vP} [Category.{wP} 𝒵] {𝒳 : Type vX} [Category.{wX} 𝒳]
  {𝒴' : Type vY'} [Category.{wY'} 𝒴'] {𝒴 : Type vY} [Category.{wY} 𝒴]
  (a : 𝒵 ⥤ 𝒳) (b : 𝒵 ⥤ 𝒴') (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴) (w : TwoSquare a b f g)

/-- **The base change map on compatible sections.** A compatible family `s` of sections of `F`
over `g(y') ↓ f` gives the compatible family over `y' ↓ b` whose value at `(z, ψ : b z → y')`
is the value of `s` at `(a z, w_z ≫ g ψ)`. -/
def sectionsBaseChange (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{m}) (y' : 𝒴'ᵒᵖ) :
    compatibleSections f.op F (g.op.obj y') →+ compatibleSections b.op (a.op ⋙ F) y' where
  toFun s := ⟨fun z ψ => s.val (a.op.obj z) (g.op.map ψ ≫ w.op.app z), by
    intro z z' c ψ
    change F.map (a.op.map c) (s.val (a.op.obj z) (g.op.map ψ ≫ w.op.app z)) =
      s.val (a.op.obj z') (g.op.map (ψ ≫ b.op.map c) ≫ w.op.app z')
    rw [s.property (a.op.obj z) (a.op.obj z') (a.op.map c)]
    refine congrArg (s.val (a.op.obj z')) ?_
    rw [Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (g.op.map ψ ≫ ·) (w.op.naturality c).symm⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The value of `sectionsBaseChange a b f g w F y' s` at `(z, ψ)` is the value of `s` at
`(a z, w_z ≫ g ψ)`, as in its definition. -/
@[simp]
lemma sectionsBaseChange_apply (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{m}) (y' : 𝒴'ᵒᵖ)
    (s : compatibleSections f.op F (g.op.obj y')) (z : 𝒵ᵒᵖ) (ψ : y' ⟶ b.op.obj z) :
    (sectionsBaseChange a b f g w F y' s).val z ψ =
      s.val (a.op.obj z) (g.op.map ψ ≫ w.op.app z) := rfl

/-- **Base change of compatible sections along a Guitart exact square is bijective.** The map is
restriction of sections along the comparison functor of comma categories
`CategoryTheory.TwoSquare.structuredArrowDownwards` of the opposite square, which Guitart
exactness makes initial. -/
theorem bijective_sectionsBaseChange [w.GuitartExact] (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{m})
    (y' : 𝒴'ᵒᵖ) : Function.Bijective (sectionsBaseChange a b f g w F y') := by
  let Φ := w.op.structuredArrowDownwards y'
  let Q := StructuredArrow.proj (g.op.obj y') f.op ⋙ F ⋙ forget AddCommGrpCat
  have hbij := Functor.bijective_sectionsPrecomp Φ Q
  refine ⟨fun s t hst => ?_, fun t => ?_⟩
  · apply compatibleSectionsToSections_injective
    apply hbij.1
    apply Subtype.ext
    funext j
    exact congrArg (fun r => r.val j.right j.hom) hst
  · obtain ⟨s₀, hs₀⟩ := hbij.2 (compatibleSectionsToSections b.op (a.op ⋙ F) y' t)
    refine ⟨sectionsToCompatibleSections f.op F (g.op.obj y') s₀, ?_⟩
    apply Subtype.ext
    funext z ψ
    exact congrArg (fun r => r.val (StructuredArrow.mk ψ)) hs₀

end SectionsBaseChange

/-! ### The base change isomorphism on presheaves of modules -/

section ModuleSectionsBaseChange

universe U

variable {𝒵 : Type vP} [Category.{wP} 𝒵] {𝒳 : Type vX} [Category.{wX} 𝒳]
  {𝒴' : Type vY'} [Category.{wY'} 𝒴'] {𝒴 : Type vY} [Category.{wY} 𝒴]
  (a : 𝒵 ⥤ 𝒳) (b : 𝒵 ⥤ 𝒴') (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴) (w : TwoSquare a b f g)
  (R : 𝒴ᵒᵖ ⥤ RingCat.{u}) (ha : b.op ⋙ g.op ⋙ R = a.op ⋙ f.op ⋙ R)
  (hRw : ∀ z : 𝒵ᵒᵖ, R.map (w.op.app z) = eqToHom (Functor.congr_obj ha z))

attribute [local instance] restrictedSectionModule sectionsModule

include hRw in
/-- The component at `M` and `y'` of the base change map of presheaves of modules: the base change
map of compatible sections, which is linear because the 2-cell acts on scalars by identities. -/
noncomputable def moduleSectionsBaseChangeApp
    (M : PresheafOfModules.{max u vP wP vX wX vY' wY' vY wY U} (f.op ⋙ R)) (y' : 𝒴'ᵒᵖ) :
    ((PresheafOfModules.pushforward₀ g R).obj
        ((moduleSectionsFunctor.{u, vX, wX, max u vP wP vX wX vY' wY' vY wY U} f R).obj M)).obj
          y' ⟶
      ((moduleSectionsFunctor.{u, vP, wP, max u vP wP vX wX vY' wY' vY wY U} b (g.op ⋙ R)).obj
        ((PresheafOfModules.restrictScalars (eqToHom ha)).obj
          ((PresheafOfModules.pushforward₀ a (f.op ⋙ R)).obj M))).obj y' :=
  ModuleCat.ofHom
    { toFun := sectionsBaseChange a b f g w M.presheaf y'
      map_add' := map_add _
      map_smul' := fun r s => by
        apply Subtype.ext
        funext z ψ
        have key : R.map (g.op.map ψ ≫ w.op.app z) r =
            (eqToHom ha).app z (R.map (g.op.map ψ) r) := by
          rw [R.map_comp, hRw z, eqToHom_app]
          rfl
        let : Module (R.obj ((a.op ⋙ f.op).obj z)) (M.presheaf.obj (a.op.obj z)) :=
          restrictedSectionModule f R M (a.op.obj z)
        exact congrArg (· • s.val (a.op.obj z) (g.op.map ψ ≫ w.op.app z)) key }

variable [w.GuitartExact]

/-- **Base change for the direct image of presheaves of modules of Stacks 06WD.** For a Guitart
exact square whose 2-cell acts on the structure rings by identities, the base change map
`f_* ⋙ g⁻¹ ⟶ a⁻¹ ⋙ b_*` on compatible-sections models is an isomorphism. -/
noncomputable def moduleSectionsBaseChangeIso :
    moduleSectionsFunctor.{u, vX, wX, max u vP wP vX wX vY' wY' vY wY U} f R ⋙
        PresheafOfModules.pushforward₀ g R ≅
      PresheafOfModules.pushforward₀ a (f.op ⋙ R) ⋙
        PresheafOfModules.restrictScalars (eqToHom ha) ⋙
          moduleSectionsFunctor.{u, vP, wP, max u vP wP vX wX vY' wY' vY wY U} b (g.op ⋙ R) :=
  NatIso.ofComponents
    (fun M => PresheafOfModules.isoMk
      (fun y' => (LinearEquiv.ofBijective
        (moduleSectionsBaseChangeApp.{u, vP, wP, vX, wX, vY', wY', vY, wY, U}
          a b f g w R ha hRw M y').hom
        (bijective_sectionsBaseChange a b f g w M.presheaf y')).toModuleIso)
      (fun y₁ y₂ c => by
        ext s
        apply Subtype.ext
        funext z ψ
        change s.val (a.op.obj z) (g.op.map c ≫ g.op.map ψ ≫ w.op.app z) =
          s.val (a.op.obj z) (g.op.map (c ≫ ψ) ≫ w.op.app z)
        rw [Functor.map_comp, Category.assoc]))
    (fun {M N} φ => by
      ext y' s
      apply Subtype.ext
      funext z ψ
      rfl)

end ModuleSectionsBaseChange

end AlgebraicGeometry.Stack

end
