module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Ring
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct images of sheaves of modules, and internal modules over an internal ring

Let `f : Sh(C) → Sh(D)` be a morphism of topoi and let `O` be a sheaf of rings on `C`. The
direct image `f_*` is a right adjoint, hence preserves finite products, so `f_*` applied to
the multiplication map `O × F ⟶ F` of a sheaf of `O`-modules, read through the product
comparison `f_*(O × F) ≅ f_*O × f_*F`, makes `f_*F` a sheaf of modules over a sheaf of rings
`f_*O`, functorially in `F`. That is Stacks 03D1, and it is the second half of this file.

The construction reuses the engine of Stacks 03D2 in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullback.lean`: that engine is stated for
an arbitrary functor `Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)` with
`[PreservesFiniteProducts Φ]` and assumes *no* adjointness, so instantiating `Φ := f.pushforward`
gives the direct image at once. In particular no transport of algebraic structure along a
morphism of topoi in the sense of Stacks 00YV is needed, and the unit `O ⟶ f_*f⁻¹O` as a map
of sheaves of *rings* — the one place where the Stacks proof of 03D3 appeals to 00YV — is
built here as `ringUnit`.

The first half of the file is an independent internal-algebra substrate: a morphism of topoi
has no site data, so the direct image of a sheaf of modules cannot be described on sections,
and what survives is that it carries the *internal* algebraic structure of a sheaf — its
operations read as morphisms out of finite products — to internal algebraic structure on the
image. This file supplies the internal module theory that such a transport needs, and the
comparisons that turn a sheaf of modules into internal data and back.

Mathlib has internal ring objects (`CategoryTheory.RingObj`, `CategoryTheory.CommRingObj`)
and the action of a monoid object on an object (`CategoryTheory.ModObj`), but no internal
*modules* over a ring object: `ModObj` records only the multiplicative action, with neither
the additive group structure of the module nor the two distributive laws. Mathlib also has
no transport of ring or module objects along a functor —
`Mathlib/CategoryTheory/Monoidal/Mon.lean` carries an explicit `TODO: mapMod`. Both gaps are filled
here.

## Main definitions

* `CategoryTheory.ModuleObj`: a module object over a ring object in a cartesian monoidal
  category — an additive commutative group object with a distributive action.
* `CategoryTheory.ModuleObj.Hom.module`: `Hom(X, M)` is a module over the ring `Hom(X, R)`.
* `CategoryTheory.Functor.modObjObj`, `.ringObjObj`, `.moduleObjObj`: the image of an action,
  of a ring object and of a module object under a finite-product-preserving functor.
* `CategoryTheory.Functor.FullyFaithful.commRingObj`, `.moduleObj`: the pullback of a ring
  object and of a module object along a fully faithful finite-product-preserving functor.
* `Stacks.InternalObj.typeCommRing`, `.typeAddCommGroup`, `.typeModule`: the ordinary
  algebraic structures carried by internal ones in `Type w`.
* `Stacks.InternalObj.evaluationCommRingObj`, `.evaluationModuleObj`: internal structure in a
  functor category, read off at an object.
* `Stacks.InternalObj.presheafCommRingObj`, `.presheafModuleObj`: the sectionwise operations of
  a presheaf of commutative rings, resp. of a presheaf of modules over one, as internal
  structure in the presheaf category.
* `Stacks.sheafCartesian`, `Stacks.sheafMonoidal`, `Stacks.sheafMonoidalStruct`,
  `Stacks.sheafBraided`, `Stacks.inclusionBraided`: the cartesian monoidal structure on sheaves
  of sets given by the chosen products `⨯`, and the braidings over it. These are not global
  instances (Mathlib's sectionwise structure is the default); `open scoped Stacks.SheafLimitsProd`
  makes the whole suite the instance.
* `Stacks.sheafCommRingObj`, `Stacks.sheafModuleObj`: the same for a sheaf of commutative rings
  and a sheaf of modules over it, in the cartesian monoidal category of sheaves of sets with the
  products `⨯` of `Stacks.sheafCartesian`.
* `Stacks.Sheaves.ToposPushforward.pushforwardRingSheaf`: the direct image of a sheaf of rings
  along a morphism of topoi, with `pushforwardRingSheafIso` identifying its underlying sheaf of
  sets with the direct image of the underlying sheaf of sets.
* `Stacks.Sheaves.ToposPushforward.pushforwardModuleObj`, `.pushforwardModuleFunctor`: the
  direct image of a sheaf of modules, and its functoriality.
* `Stacks.Sheaves.ToposPushforward.PushforwardModuleData`: the data packaging the direct-image
  ring, the functor on modules, their identifications with ordinary direct images, and the
  equations identifying every transported operation with the direct image of the original one.
* `Stacks.Sheaves.ToposPushforward.pushforwardProdIso`: the product comparison
  `f_*(A × B) ≅ f_*A × f_*B`, which is the isomorphism Stacks 03D1 applies to the
  multiplication map.
* `Stacks.Sheaves.ToposPushforward.ringUnit`: the unit `O ⟶ f_*f⁻¹O` as a morphism of sheaves
  of rings.

## Main results

* `Stacks.Sheaves.ToposPushforward.pushforwardModule` (Stacks 03D1): the direct image of a
  sheaf of `O`-modules along a morphism of topoi is a sheaf of modules over the direct-image
  ring, with scalar multiplication the direct image of the original scalar multiplication read
  through the product comparison, functorially in the module.
* `Stacks.Sheaves.ToposPushforward.PushforwardModuleData.action_eq`: the same equation solved
  for the action, exhibiting it as built from `f_*` of the multiplication map.
* `Stacks.Sheaves.ToposPushforward.ringAddObj_comp`, `.ringMulObj_comp`, `.ringNegObj_comp`,
  `.ringZeroObj_comp`, `.ringOneObj_comp`: transporting a ring structure in two steps, along
  `Φ` and then along `Ψ`, gives the same operations as transporting it in one step along
  `Φ ⋙ Ψ`. This is what makes `ringUnit` a ring map.

* `CategoryTheory.smul_add_iff`, `CategoryTheory.add_smul_iff`: the two distributive laws for an
  internal action, as equations of morphisms, hold exactly when they hold on all generalized
  elements. These are the module analogues of `CategoryTheory.mul_add_iff` and
  `CategoryTheory.add_mul_iff`, and they are what makes every proof below a one-line
  reduction to ordinary algebra.

## Implementation notes

The distributive laws are stated as single equations of morphisms at the universal generalized
elements, exactly as `CategoryTheory.RingObj` states `mul_add` and `add_mul`, rather than as
universally quantified statements about generalized elements. This keeps `ModuleObj` a
structure with finitely much data, and the `_iff` lemmas convert in both directions.

`ModuleObj R M` *extends* `AddGrpObj M` and `IsCommAddMonObj M` rather than taking them as
instance parameters, mirroring `RingObj`. This is what makes transport along a functor
expressible: the transported additive structure and the transported action have to be
assembled together, and a module object over the transported ring object is then a single
piece of data rather than a structure over an instance that must be supplied separately.

`forgetCommRingSheaf` assumes `J.HasSheafCompose (forget₂ CommRingCat RingCat)` instead of
deriving it. Deriving it requires `PreservesLimit F (forget CommRingCat)` for index categories
of the site's size, and in the pinned Mathlib every `PreservesLimitsOfSize` instance for the
ring forgetful functors carries `[UnivLE.{v, u}]`; at an arbitrary site size that is the
hypothesis `UnivLE.{v, w}`, comparing the site's hom universe with the universe of sections.
Assuming the `HasSheafCompose` instance is how the sibling statements in this development
carry it, and it restricts no intended application.

The two sites and the section universes are independent throughout: nothing here relates the
universe of the site to the universe in which sections live, and no universe is specialized.

The direct image is stated for a sheaf of *rings*, matching the Stacks statement of 03D1 and
the library's statement of the companion Tag 03D2; commutativity is nowhere used and nowhere asserted.
`PushforwardModuleData` is a field-for-field mirror of
`Stacks.Sheaves.ToposPullback.PullbackModuleData`, which is forced: its `ringIso` and
`moduleIso` are `Iso.refl` here too, because the underlying sheaf of sets of the direct-image
ring **is** `f_*` of the underlying sheaf, on the nose.

`MorphismOfTopoi.preservesFiniteProductsPushforward` is registered as an instance rather than
produced by a local `haveI` at each use. This is forced by `ringUnit`, whose *type* mentions
`inverseImageRingSheaf`, which depends on the instance; a local `haveI` would make the two
occurrences of the instance distinct terms. Both new instances are keyed on
`MorphismOfTopoi.pushforward`/`.inverseImage` and so cannot fire anywhere else.

`Sheaf.ringSheaf (pullbackRingSheaf J Φ O)` and `Φ.obj (Sheaf.ringSheaf O)` are definitionally
equal, but only at default transparency: seeing it requires unfolding `pullbackRingSheaf`.
`rw` and `simp`, which work at instance transparency, therefore cannot bridge the two
spellings, which is why the `*_comp` lemmas below are assembled from explicitly typed `have`
steps rather than proved by rewriting.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1), the direct image of a
  sheaf of modules along a morphism of topoi, whose scalar action is obtained from
  preservation of binary products.
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2), the inverse image,
  whose engine is reused here.
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV), that a morphism of
  topoi transports algebraic structure. Not used: see the module introduction.

Tags covered: 03D1.
-/

@[expose] public section

universe v u v' u' w w'

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AddMonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Left distributivity of an internal action over the addition of the module, read on
generalized elements. This is the module analogue of `CategoryTheory.mul_add_iff`. -/
lemma smul_add_iff (R M : C) [MonObj R] [AddMonObj M] [ModObj R M] :
    R ◁ σ ≫ γ[R, M] = lift ((R ◁ fst M M) ≫ γ[R, M]) ((R ◁ snd M M) ≫ γ[R, M]) ≫ σ ↔
      ∀ ⦃X : C⦄ (a : X ⟶ R) (b c : X ⟶ M), a • (b + c) = a • b + a • c := by
  refine ⟨fun h _ a b c ↦ ?_, fun h ↦ ?_⟩
  · have := lift a (lift b c) ≫= h
    simp only [lift_whiskerLeft_assoc] at this
    simp only [Hom.add_def, Hom.smul_def, this, ← Category.assoc]
    cat_disch
  · replace h := h (fst R (M ⊗ M)) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)
    simp only [Hom.smul_def, Hom.add_def] at h
    convert! h using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch

/-- Right distributivity of an internal action over the addition of the ring, read on
generalized elements. This is the module analogue of `CategoryTheory.add_mul_iff`. -/
lemma add_smul_iff (R M : C) [MonObj R] [AddMonObj R] [AddMonObj M] [ModObj R M] :
    σ ▷ M ≫ γ[R, M] = lift (fst R R ▷ M ≫ γ[R, M]) (snd R R ▷ M ≫ γ[R, M]) ≫ σ ↔
      ∀ ⦃X : C⦄ (a b : X ⟶ R) (c : X ⟶ M), (a + b) • c = a • c + b • c := by
  refine ⟨fun h _ a b c ↦ ?_, fun h ↦ ?_⟩
  · have := lift (lift a b) c ≫= h
    simp only [lift_whiskerRight_assoc] at this
    simp only [Hom.add_def, Hom.smul_def, this, ← Category.assoc]
    cat_disch
  · replace h := h (fst (R ⊗ R) M ≫ fst _ _) (fst _ _ ≫ snd _ _) (snd _ _)
    simp only [Hom.smul_def, Hom.add_def] at h
    convert! h using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch

/-- Compatibility of an internal action with multiplication, written with the whiskerings of
the cartesian monoidal structure rather than with the notation of a general monoidal action. -/
lemma ModObj.mul_smul' (R M : C) [MonObj R] [ModObj R M] :
    μ ▷ M ≫ γ[R, M] = (α_ R R M).hom ≫ R ◁ γ[R, M] ≫ γ[R, M] :=
  ModObj.mul_smul (M := R) (X := M)

variable [BraidedCategory C]

/-- A *module object* over a ring object `R` in a cartesian monoidal category is an additive
commutative group object `M` together with an action `R ⊗ M ⟶ M` of the multiplicative monoid
of `R` which is distributive on both sides.

This is the internal counterpart of `Module`, and the module analogue of
`CategoryTheory.RingObj`. Mathlib's `CategoryTheory.ModObj` records only the action of the
multiplicative monoid; the two distributivity laws are the extra content. -/
@[ega "0 8.2.3"]
class ModuleObj (R M : C) [RingObj R] extends AddGrpObj M, IsCommAddMonObj M, ModObj R M where
  /-- Scalar multiplication distributes over the addition of the module. -/
  smul_add (R M) : R ◁ σ ≫ γ[R, M] =
    lift ((R ◁ fst M M) ≫ γ[R, M]) ((R ◁ snd M M) ≫ γ[R, M]) ≫ σ
  /-- Scalar multiplication distributes over the addition of the ring. -/
  add_smul (R M) : σ ▷ M ≫ γ[R, M] =
    lift (fst R R ▷ M ≫ γ[R, M]) (snd R R ▷ M ≫ γ[R, M]) ≫ σ

namespace ModuleObj

open scoped RingObj

variable {R M : C} [RingObj R] [ModuleObj R M] {X : C}

lemma Hom.smul_add (a : X ⟶ R) (b c : X ⟶ M) : a • (b + c) = a • b + a • c := by
  revert X a b c
  rw [← smul_add_iff]
  exact ModuleObj.smul_add R M

lemma Hom.add_smul (a b : X ⟶ R) (c : X ⟶ M) : (a + b) • c = a • c + b • c := by
  revert X a b c
  rw [← add_smul_iff]
  exact ModuleObj.add_smul R M

/-- If `M` is a module object over a ring object `R`, then `Hom(X, M)` is a module over the
ring `Hom(X, R)`. -/
abbrev Hom.module : Module (X ⟶ R) (X ⟶ M) where
  smul_add := Hom.smul_add
  add_smul := Hom.add_smul
  smul_zero a := by
    have h := Hom.smul_add a (0 : X ⟶ M) 0
    simpa using h
  zero_smul c := by
    have h := Hom.add_smul (0 : X ⟶ R) 0 c
    simpa using h

scoped[CategoryTheory.ModuleObj] attribute [instance] ModuleObj.Hom.module

end ModuleObj

namespace Functor

variable {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D) [F.Braided]

open scoped Obj RingObj ModuleObj

/-- The image of an internal action under a finite-product-preserving functor. -/
noncomputable abbrev modObjObj (R M : C) [MonObj R] [ModObj R M] :
    ModObj (F.obj R) (F.obj M) where
  smul := LaxMonoidal.μ F R M ≫ F.map γ[R, M]
  one_smul := by
    change (η : _ ⟶ F.obj R) ▷ F.obj M ≫ LaxMonoidal.μ F R M ≫ F.map γ[R, M] = (λ_ _).hom
    simp [← F.map_comp]
  mul_smul := by
    change μ ▷ F.obj M ≫ LaxMonoidal.μ F R M ≫ F.map γ[R, M] =
      (α_ _ _ _).hom ≫ F.obj R ◁ (LaxMonoidal.μ F R M ≫ F.map γ[R, M]) ≫
        LaxMonoidal.μ F R M ≫ F.map γ[R, M]
    rw [Functor.obj.μ_def]
    simp_rw [comp_whiskerRight, Category.assoc, LaxMonoidal.μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, LaxMonoidal.μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, ModObj.mul_smul']
    simp

/-- The image of a ring object under a finite-product-preserving functor. -/
noncomputable abbrev ringObjObj (R : C) [RingObj R] : RingObj (F.obj R) where
  __ := F.addGrpObjObj
  __ := F.monObjObj R
  toIsCommAddMonObj := {
    add_comm := by
      dsimp
      rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp,
        IsCommAddMonObj.add_comm] }
  mul_add := by
    rw [mul_add_iff]
    intro X a b c
    let k := lift a (lift b c ≫ Functor.LaxMonoidal.μ F R R) ≫
      Functor.LaxMonoidal.μ F R (R ⊗ R)
    have h := congrArg (fun t => k ≫ F.map t)
      (_root_.mul_add (fst R (R ⊗ R)) (snd R (R ⊗ R) ≫ fst R R)
        (snd R (R ⊗ R) ≫ snd R R))
    simpa [Functor.map_mul, Functor.map_add', MonObj.comp_mul, AddMonObj.comp_add,
      k, Functor.map_comp] using h
  add_mul := by
    rw [add_mul_iff]
    intro X a b c
    let k := lift a (lift b c ≫ Functor.LaxMonoidal.μ F R R) ≫
      Functor.LaxMonoidal.μ F R (R ⊗ R)
    have h := congrArg (fun t => k ≫ F.map t)
      (_root_.add_mul (fst R (R ⊗ R)) (snd R (R ⊗ R) ≫ fst R R)
        (snd R (R ⊗ R) ≫ snd R R))
    simpa [Functor.map_mul, Functor.map_add', MonObj.comp_mul, AddMonObj.comp_add,
      k, Functor.map_comp] using h

scoped[CategoryTheory.Obj] attribute [instance] CategoryTheory.Functor.modObjObj
  CategoryTheory.Functor.ringObjObj

/-- A finite-product-preserving functor commutes with an internal scalar multiplication. -/
protected lemma map_smul' (R M : C) [MonObj R] [ModObj R M] {X : C} (a : X ⟶ R) (b : X ⟶ M) :
    F.map (a • b) = F.map a • F.map b := by
  show F.map (lift a b ≫ γ[R, M]) =
    lift (F.map a) (F.map b) ≫ LaxMonoidal.μ F R M ≫ F.map γ[R, M]
  rw [Monoidal.lift_μ_assoc, F.map_comp]

/-- The image of a module object under a finite-product-preserving functor. -/
noncomputable abbrev moduleObjObj (R M : C) [RingObj R] [ModuleObj R M] :
    ModuleObj (F.obj R) (F.obj M) where
  __ := F.addGrpObjObj
  __ := F.modObjObj R M
  toIsCommAddMonObj := {
    add_comm := by
      dsimp
      rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp,
        IsCommAddMonObj.add_comm] }
  smul_add := by
    rw [smul_add_iff]
    intro X a b c
    let k := lift a (lift b c ≫ Functor.LaxMonoidal.μ F M M) ≫
      Functor.LaxMonoidal.μ F R (M ⊗ M)
    have h := congrArg (fun t => k ≫ F.map t)
      (ModuleObj.Hom.smul_add (fst R (M ⊗ M)) (snd R (M ⊗ M) ≫ fst M M)
        (snd R (M ⊗ M) ≫ snd M M))
    simpa [-smul_add, Functor.map_smul', Functor.map_add', ModObj.comp_smul,
      AddMonObj.comp_add, k, Functor.map_comp] using h
  add_smul := by
    rw [add_smul_iff]
    intro X a b c
    let k := lift (lift a b ≫ Functor.LaxMonoidal.μ F R R) c ≫
      Functor.LaxMonoidal.μ F (R ⊗ R) M
    have h := congrArg (fun t => k ≫ F.map t)
      (ModuleObj.Hom.add_smul (fst (R ⊗ R) M ≫ fst R R) (fst (R ⊗ R) M ≫ snd R R)
        (snd (R ⊗ R) M))
    simpa [Functor.map_smul', Functor.map_add', ModObj.comp_smul,
      AddMonObj.comp_add, k, Functor.map_comp] using h

scoped[CategoryTheory.Obj] attribute [instance] CategoryTheory.Functor.moduleObjObj


end Functor

namespace Functor

variable {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} [F.Braided] (hF : F.FullyFaithful)

open scoped RingObj CommRingObj


/-- Pull a commutative ring object back along a fully faithful finite-product-preserving
functor. -/
noncomputable abbrev FullyFaithful.commRingObj (R : C) [CommRingObj (F.obj R)] :
    CommRingObj R := by
  letI : AddGrpObj (F.obj R) := inferInstance
  letI : AddMonObj (F.obj R) := inferInstance
  letI : MonObj (F.obj R) := inferInstance
  letI hM : F.Monoidal := inferInstance
  letI : F.OplaxMonoidal := hM.toOplaxMonoidal
  letI := hF.addGrpObj R
  letI := hF.monObj R
  exact {
    toIsCommAddMonObj := { add_comm := hF.map_injective (by
      simp [Functor.map_comp, IsCommAddMonObj.add_comm]) }
    toIsCommMonObj := { mul_comm := hF.map_injective (by
      simp [Functor.map_comp, IsCommMonObj.mul_comm]) }
    mul_add := by
      apply (mul_add_iff R).mpr
      intro Y a b c
      apply hF.map_injective
      have hm : (MonObj.mul (X := R)) = hF.preimage
          (Functor.OplaxMonoidal.δ F R R ≫ MonObj.mul) := rfl
      have ha : (AddMonObj.add (X := R)) = hF.preimage
          (Functor.OplaxMonoidal.δ F R R ≫ AddMonObj.add) := rfl
      dsimp +zetaDelta only [Hom.mul_def, Hom.add_def]
      change F.map (lift a (lift b c ≫ hF.preimage
          (Functor.OplaxMonoidal.δ F R R ≫ AddMonObj.add)) ≫ hF.preimage
          (Functor.OplaxMonoidal.δ F R R ≫ MonObj.mul)) =
        F.map (lift (lift a b ≫ hF.preimage (Functor.OplaxMonoidal.δ F R R ≫ MonObj.mul))
          (lift a c ≫ hF.preimage (Functor.OplaxMonoidal.δ F R R ≫ MonObj.mul)) ≫
          hF.preimage (Functor.OplaxMonoidal.δ F R R ≫ AddMonObj.add))
      simpa only [Hom.mul_def, Hom.add_def, Functor.map_comp,
        Functor.FullyFaithful.map_preimage, Category.assoc,
        Functor.OplaxMonoidal.lift_δ_assoc] using
        _root_.mul_add (F.map a) (F.map b) (F.map c)
    add_mul := by
      apply (add_mul_iff R).mpr
      intro Y a b c
      apply hF.map_injective
      have hm : (MonObj.mul (X := R)) = hF.preimage
          (Functor.OplaxMonoidal.δ F R R ≫ MonObj.mul) := rfl
      have ha : (AddMonObj.add (X := R)) = hF.preimage
          (Functor.OplaxMonoidal.δ F R R ≫ AddMonObj.add) := rfl
      dsimp +zetaDelta only [Hom.mul_def, Hom.add_def]
      change F.map (lift (lift a b ≫ hF.preimage
          (Functor.OplaxMonoidal.δ F R R ≫ AddMonObj.add)) c ≫ hF.preimage
          (Functor.OplaxMonoidal.δ F R R ≫ MonObj.mul)) =
        F.map (lift (lift a c ≫ hF.preimage (Functor.OplaxMonoidal.δ F R R ≫ MonObj.mul))
          (lift b c ≫ hF.preimage (Functor.OplaxMonoidal.δ F R R ≫ MonObj.mul)) ≫
          hF.preimage (Functor.OplaxMonoidal.δ F R R ≫ AddMonObj.add))
      simpa only [Hom.mul_def, Hom.add_def, Functor.map_comp,
        Functor.FullyFaithful.map_preimage, Category.assoc,
        Functor.OplaxMonoidal.lift_δ_assoc] using
        _root_.add_mul (F.map a) (F.map b) (F.map c) }

open scoped ModuleObj in
/-- Pull a module object back along a fully faithful finite-product-preserving functor. -/
noncomputable abbrev FullyFaithful.moduleObj (R M : C) [CommRingObj (F.obj R)]
    [ModuleObj (F.obj R) (F.obj M)] :
    letI := hF.commRingObj R
    ModuleObj R M := by
  letI : AddGrpObj (F.obj M) := inferInstance
  letI : AddMonObj (F.obj M) := inferInstance
  letI : AddGrpObj (F.obj R) := inferInstance
  letI : AddMonObj (F.obj R) := inferInstance
  letI : MonObj (F.obj R) := inferInstance
  letI hM : F.Monoidal := inferInstance
  letI : F.OplaxMonoidal := hM.toOplaxMonoidal
  letI := hF.commRingObj R
  letI := hF.addGrpObj M
  letI mod : ModObj R M := {
    smul := hF.preimage (Functor.OplaxMonoidal.δ F R M ≫ γ[F.obj R, F.obj M])
    one_smul := hF.map_injective (by
      simp [Functor.map_comp, ← Functor.OplaxMonoidal.δ_natural_left_assoc])
    mul_smul := hF.map_injective (by
      simp [Functor.map_comp, ← Functor.OplaxMonoidal.δ_natural_left_assoc,
        ← Functor.OplaxMonoidal.δ_natural_right_assoc]) }
  exact {
    toIsCommAddMonObj := { add_comm := hF.map_injective (by
      simp [Functor.map_comp, IsCommAddMonObj.add_comm]) }
    __ := mod
    smul_add := by
      apply (smul_add_iff R M).mpr
      intro Y a b c
      apply hF.map_injective
      have hs : (ModObj.smul (M := R) (X := M)) = hF.preimage
          (Functor.OplaxMonoidal.δ F R M ≫ γ[F.obj R, F.obj M]) := rfl
      have ha : (AddMonObj.add (X := M)) = hF.preimage
          (Functor.OplaxMonoidal.δ F M M ≫ AddMonObj.add) := rfl
      dsimp +zetaDelta only [Hom.smul_def, Hom.add_def]
      change F.map (lift a (lift b c ≫ hF.preimage
          (Functor.OplaxMonoidal.δ F M M ≫ AddMonObj.add)) ≫ hF.preimage
          (Functor.OplaxMonoidal.δ F R M ≫ γ[F.obj R, F.obj M])) =
        F.map (lift (lift a b ≫ hF.preimage
            (Functor.OplaxMonoidal.δ F R M ≫ γ[F.obj R, F.obj M]))
          (lift a c ≫ hF.preimage
            (Functor.OplaxMonoidal.δ F R M ≫ γ[F.obj R, F.obj M])) ≫
          hF.preimage (Functor.OplaxMonoidal.δ F M M ≫ AddMonObj.add))
      simpa only [Hom.smul_def, Hom.add_def, Functor.map_comp,
        Functor.FullyFaithful.map_preimage, Category.assoc,
        Functor.OplaxMonoidal.lift_δ_assoc] using
        ModuleObj.Hom.smul_add (F.map a) (F.map b) (F.map c)
    add_smul := by
      apply (add_smul_iff R M).mpr
      intro Y a b c
      apply hF.map_injective
      have hs : (ModObj.smul (M := R) (X := M)) = hF.preimage
          (Functor.OplaxMonoidal.δ F R M ≫ γ[F.obj R, F.obj M]) := rfl
      have ha : (AddMonObj.add (X := R)) = hF.preimage
          (Functor.OplaxMonoidal.δ F R R ≫ AddMonObj.add) := rfl
      dsimp +zetaDelta only [Hom.smul_def, Hom.add_def]
      change F.map (lift (lift a b ≫ hF.preimage
          (Functor.OplaxMonoidal.δ F R R ≫ AddMonObj.add)) c ≫ hF.preimage
          (Functor.OplaxMonoidal.δ F R M ≫ γ[F.obj R, F.obj M])) =
        F.map (lift (lift a c ≫ hF.preimage
            (Functor.OplaxMonoidal.δ F R M ≫ γ[F.obj R, F.obj M]))
          (lift b c ≫ hF.preimage
            (Functor.OplaxMonoidal.δ F R M ≫ γ[F.obj R, F.obj M])) ≫
          hF.preimage (Functor.OplaxMonoidal.δ F M M ≫ AddMonObj.add))
      simpa only [Hom.smul_def, Hom.add_def, Functor.map_comp,
        Functor.FullyFaithful.map_preimage, Category.assoc,
        Functor.OplaxMonoidal.lift_δ_assoc] using
        ModuleObj.Hom.add_smul (F.map a) (F.map b) (F.map c) }


end Functor

end CategoryTheory

namespace Stacks.InternalObj

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AddMonObj CommRingObj ModuleObj RingObj

/-- Evaluation at the unique point identifies a type with the maps to it from the terminal
type. This is the comparison that turns an internal algebraic structure on a type into an
ordinary one. -/
def typeHomEquiv (R : Type w) : R ≃ (PUnit.{w + 1} ⟶ R) where
  toFun r := ↾fun _ => r
  invFun a := a PUnit.unit
  left_inv _ := rfl
  right_inv a := by ext x; cases x; rfl

/-- The ordinary commutative ring carried by an internal commutative ring object in types. -/
noncomputable abbrev typeCommRing (R : Type w) [CommRingObj R] : CommRing R :=
  (typeHomEquiv R).commRing

/-- The ordinary additive commutative group carried by an internal module object in types. -/
noncomputable abbrev typeAddCommGroup (R M : Type w) [RingObj R] [ModuleObj R M] :
    AddCommGroup M :=
  (typeHomEquiv M).addCommGroup

/-- The ordinary module carried by an internal module object in types. -/
noncomputable abbrev typeModule (R M : Type w) [CommRingObj R] [ModuleObj R M] :
    letI := typeCommRing R
    letI := typeAddCommGroup R M
    Module R M :=
  letI := typeCommRing R
  letI := typeAddCommGroup R M
  letI : Module (PUnit.{w + 1} ⟶ R) M := (Equiv.addEquiv (typeHomEquiv M)).module _
  Module.compHom M (Equiv.ringEquiv (typeHomEquiv R)).toRingHom


section Evaluation

variable {C : Type u} [Category.{v} C]

/-- Evaluate every operation of an internal commutative ring object in a functor category. -/
noncomputable abbrev evaluationCommRingObj (R : C ⥤ Type w) [CommRingObj R] (X : C) :
    CommRingObj (R.obj X) where
  zero := (AddMonObj.zero (X := R)).app X
  add := (AddMonObj.add (X := R)).app X
  neg := (AddGrpObj.neg (X := R)).app X
  one := (MonObj.one (X := R)).app X
  mul := (MonObj.mul (X := R)).app X
  zero_add := congr_app (AddMonObj.zero_add R) X
  add_zero := congr_app (AddMonObj.add_zero R) X
  add_assoc := congr_app (AddMonObj.add_assoc R) X
  left_neg := congr_app (AddGrpObj.left_neg R) X
  right_neg := congr_app (AddGrpObj.right_neg R) X
  add_comm := congr_app (IsCommAddMonObj.add_comm R) X
  one_mul := congr_app (MonObj.one_mul R) X
  mul_one := congr_app (MonObj.mul_one R) X
  mul_assoc := congr_app (MonObj.mul_assoc R) X
  mul_comm := congr_app (IsCommMonObj.mul_comm R) X
  mul_add := congr_app (RingObj.mul_add R) X
  add_mul := congr_app (RingObj.add_mul R) X

/-- Evaluate every operation of an internal module object in a functor category. -/
noncomputable abbrev evaluationModuleObj (R M : C ⥤ Type w) [CommRingObj R] [ModuleObj R M]
    (X : C) :
    letI := evaluationCommRingObj R X
    ModuleObj (R.obj X) (M.obj X) :=
  letI := evaluationCommRingObj R X
  { zero := (AddMonObj.zero (X := M)).app X
    add := (AddMonObj.add (X := M)).app X
    neg := (AddGrpObj.neg (X := M)).app X
    zero_add := congr_app (AddMonObj.zero_add M) X
    add_zero := congr_app (AddMonObj.add_zero M) X
    add_assoc := congr_app (AddMonObj.add_assoc M) X
    left_neg := congr_app (AddGrpObj.left_neg M) X
    right_neg := congr_app (AddGrpObj.right_neg M) X
    add_comm := congr_app (IsCommAddMonObj.add_comm M) X
    smul := (ModObj.smul (M := R) (X := M)).app X
    one_smul := congr_app (ModObj.one_smul (M := R) M) X
    mul_smul := congr_app (ModObj.mul_smul (M := R) M) X
    smul_add := congr_app (ModuleObj.smul_add R M) X
    add_smul := congr_app (ModuleObj.add_smul R M) X }

end Evaluation


section Presheaf

variable {C : Type u} [Category.{v} C]

/-- The sectionwise ring operations of a commutative-ring-valued presheaf, as an internal
commutative ring object of the presheaf category. -/
noncomputable abbrev presheafCommRingObj (R : C ⥤ CommRingCat.{w}) :
    CommRingObj (R ⋙ forget CommRingCat) where
  zero := { app X := ↾fun _ => (0 : (R.obj X : Type w))
            naturality X Y f := by ext; exact (map_zero (R.map f).hom).symm }
  add := { app X := ↾fun p => id (α := (R.obj X : Type w)) p.1 + id (α := (R.obj X : Type w)) p.2
           naturality X Y f := by ext; exact (map_add (R.map f).hom _ _).symm }
  neg := { app X := ↾fun a => -id (α := (R.obj X : Type w)) a
           naturality X Y f := by ext; exact (map_neg (R.map f).hom _).symm }
  one := { app X := ↾fun _ => (1 : (R.obj X : Type w))
           naturality X Y f := by ext; exact (map_one (R.map f).hom).symm }
  mul := { app X := ↾fun p => id (α := (R.obj X : Type w)) p.1 * id (α := (R.obj X : Type w)) p.2
           naturality X Y f := by ext; exact (map_mul (R.map f).hom _ _).symm }
  zero_add := by ext X x; exact zero_add (id (α := (R.obj X : Type w)) x.2)
  add_zero := by ext X x; exact add_zero (id (α := (R.obj X : Type w)) x.1)
  add_assoc := by ext X x; exact add_assoc (id (α := (R.obj X : Type w)) x.1.1) x.1.2 x.2
  left_neg := by ext X x; exact neg_add_cancel (id (α := (R.obj X : Type w)) x)
  right_neg := by ext X x; exact add_neg_cancel (id (α := (R.obj X : Type w)) x)
  add_comm := by ext X x; exact add_comm (id (α := (R.obj X : Type w)) x.2) x.1
  one_mul := by ext X x; exact one_mul (id (α := (R.obj X : Type w)) x.2)
  mul_one := by ext X x; exact mul_one (id (α := (R.obj X : Type w)) x.1)
  mul_assoc := by ext X x; exact mul_assoc (id (α := (R.obj X : Type w)) x.1.1) x.1.2 x.2
  mul_comm := by ext X x; exact mul_comm (id (α := (R.obj X : Type w)) x.2) x.1
  mul_add := by ext X x; exact mul_add (id (α := (R.obj X : Type w)) x.1) x.2.1 x.2.2
  add_mul := by ext X x; exact add_mul (id (α := (R.obj X : Type w)) x.1.1) x.1.2 x.2

/-- The sectionwise module operations of a presheaf of modules over a presheaf of commutative
rings, as an internal module object of the presheaf category. -/
noncomputable abbrev presheafModuleObj (R : Cᵒᵖ ⥤ CommRingCat.{w})
    (N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) :
    letI := presheafCommRingObj R
    ModuleObj (R ⋙ forget CommRingCat) (N.presheaf ⋙ forget AddCommGrpCat) :=
  letI := presheafCommRingObj R
  { zero := { app X := ↾fun _ => (0 : N.obj X)
              naturality X Y f := by ext; exact (map_zero (N.map f).hom).symm }
    add := { app X := ↾fun p => (p.1 + p.2 : N.obj X)
             naturality X Y f := by ext; exact (map_add (N.map f).hom _ _).symm }
    neg := { app X := ↾fun a => (-a : N.obj X)
             naturality X Y f := by ext; exact (map_neg (N.map f).hom _).symm }
    smul := { app X := ↾fun p =>
                @HSMul.hSMul (R.obj X : Type w) (N.obj X : Type w) (N.obj X : Type w) _ p.1 p.2
              naturality X Y f := by ext p; exact (N.map_smul f p.1 p.2).symm }
    zero_add := by ext X x; exact zero_add (id (α := (N.obj X : Type w)) x.2)
    add_zero := by ext X x; exact add_zero (id (α := (N.obj X : Type w)) x.1)
    add_assoc := by ext X x; exact add_assoc (id (α := (N.obj X : Type w)) x.1.1) x.1.2 x.2
    left_neg := by ext X x; exact neg_add_cancel (id (α := (N.obj X : Type w)) x)
    right_neg := by ext X x; exact add_neg_cancel (id (α := (N.obj X : Type w)) x)
    add_comm := by ext X x; exact add_comm (id (α := (N.obj X : Type w)) x.2) x.1
    one_smul := by ext X x; exact one_smul (R.obj X : Type w) (id (α := (N.obj X : Type w)) x.2)
    mul_smul := by
      ext X x
      exact mul_smul (id (α := (R.obj X : Type w)) x.1.1) x.1.2
        (id (α := (N.obj X : Type w)) x.2)
    smul_add := by
      ext X x
      exact smul_add (id (α := (R.obj X : Type w)) x.1)
        (id (α := (N.obj X : Type w)) x.2.1) x.2.2
    add_smul := by
      ext X x
      exact add_smul (id (α := (R.obj X : Type w)) x.1.1) x.1.2
        (id (α := (N.obj X : Type w)) x.2) }

end Presheaf

end Stacks.InternalObj

namespace Stacks

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AddMonObj CommRingObj RingObj ModuleObj
open Stacks.InternalObj

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget CommRingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- Forgetting commutativity in a sheaf of commutative rings. This is the functor over whose
values Mathlib's sheaves of modules are taken.

The hypothesis `J.HasSheafCompose (forget₂ CommRingCat RingCat)` is assumed rather than
derived: deriving it needs `PreservesLimit F (forget CommRingCat)` for index categories of
the site's size, which in the pinned Mathlib holds only under `UnivLE.{v, w}` relating the
site's hom universe to the universe of sections. -/
noncomputable abbrev forgetCommRingSheaf
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    Sheaf J CommRingCat.{w} ⥤ Sheaf J RingCat.{w} :=
  sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})

/-- The underlying sheaf of sets of a sheaf of commutative rings. -/
noncomputable abbrev underlyingRingSheaf (O : Sheaf J CommRingCat.{w}) : Sheaf J (Type w) :=
  (sheafCompose J (forget CommRingCat.{w})).obj O

/-- The underlying sheaf of sets of a sheaf of modules. -/
noncomputable abbrev underlyingModuleSheaf {O : Sheaf J RingCat.{w'}}
    (G : SheafOfModules.{w} O) : Sheaf J (Type w) :=
  (sheafCompose J (forget AddCommGrpCat.{w})).obj ((SheafOfModules.toSheaf O).obj G)

/-! ### The internal-object cartesian structure on sheaves of sets

The default cartesian monoidal structure on `Sheaf J (Type w)` is Mathlib's
(`Mathlib/CategoryTheory/Sites/CartesianMonoidal.lean`): products are computed sectionwise, as
the full subcategory of presheaves. The internal ring and module objects of this file and of its
consumers are written instead against the chosen products `⨯` of `HasFiniteProducts`. That
structure is kept here as a named suite which is *not* a global instance: a development that
needs it opens it with `open scoped Stacks.SheafLimitsProd`, which makes `sheafCartesian`, the
monoidal structure and its `MonoidalCategoryStruct` read off from it, the braiding and the
braided inclusion into presheaves instances of high priority, so that every class on the path
`MonoidalCategoryStruct → MonoidalCategory → CartesianMonoidalCategory → BraidedCategory` is
answered by the same structure. -/

/-- Finite products `⨯` make the category of sheaves of sets cartesian monoidal. Not an instance:
Mathlib's sectionwise structure is the default, and this one is activated by
`open scoped Stacks.SheafLimitsProd`. -/
@[instance_reducible]
noncomputable def sheafCartesian : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts

/-- The monoidal structure underlying `sheafCartesian`. -/
@[instance_reducible]
noncomputable def sheafMonoidal : MonoidalCategory (Sheaf J (Type w)) :=
  (sheafCartesian J).toMonoidalCategory

/-- The tensor data underlying `sheafCartesian`. -/
@[instance_reducible]
noncomputable def sheafMonoidalStruct : MonoidalCategoryStruct (Sheaf J (Type w)) :=
  (sheafMonoidal J).toMonoidalCategoryStruct

/-- Products of sheaves of sets for `sheafCartesian` are symmetric. -/
@[instance_reducible]
noncomputable def sheafBraided : @BraidedCategory (Sheaf J (Type w)) _ (sheafMonoidal J) :=
  @BraidedCategory.ofCartesianMonoidalCategory _ _ (sheafCartesian J)

scoped[Stacks.SheafLimitsProd] attribute [instance high] Stacks.sheafCartesian
  Stacks.sheafMonoidal Stacks.sheafMonoidalStruct Stacks.sheafBraided

open scoped Stacks.SheafLimitsProd

/-- The inclusion of sheaves into presheaves preserves the chosen finite products of
`sheafCartesian`. -/
@[instance_reducible]
noncomputable def inclusionBraided : (sheafToPresheaf J (Type w)).Braided :=
  Functor.Braided.ofChosenFiniteProducts _

scoped[Stacks.SheafLimitsProd] attribute [instance high] Stacks.inclusionBraided

/-- The internal commutative ring object carried by the underlying sheaf of sets of a sheaf
of commutative rings. -/
noncomputable abbrev sheafCommRingObj (O : Sheaf J CommRingCat.{w}) :
    CommRingObj (underlyingRingSheaf J O) := by
  letI : CommRingObj ((sheafToPresheaf J (Type w)).obj (underlyingRingSheaf J O)) :=
    presheafCommRingObj O.obj
  exact Functor.FullyFaithful.commRingObj (fullyFaithfulSheafToPresheaf J (Type w)) _

/-- The internal module object carried by the underlying sheaf of sets of a sheaf of modules
over the underlying sheaf of sets of its sheaf of commutative rings. -/
noncomputable abbrev sheafModuleObj [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    letI := sheafCommRingObj J O
    ModuleObj (underlyingRingSheaf J O) (underlyingModuleSheaf J G) := by
  letI : CommRingObj ((sheafToPresheaf J (Type w)).obj (underlyingRingSheaf J O)) :=
    presheafCommRingObj O.obj
  letI : ModuleObj ((sheafToPresheaf J (Type w)).obj (underlyingRingSheaf J O))
      ((sheafToPresheaf J (Type w)).obj (underlyingModuleSheaf J G)) :=
    presheafModuleObj O.obj G.val
  exact Functor.FullyFaithful.moduleObj (fullyFaithfulSheafToPresheaf J (Type w)) _ _

end Stacks

/-! ## Left exactness and finite products for a morphism of topoi -/

namespace MorphismOfTopoi

universe tt ww ww' vv uu vv' uu'

open CategoryTheory Limits

variable {E : Type uu} [Category.{vv} E] {F : Type uu'} [Category.{vv'} F]
  (f : MorphismOfTopoi E F)

/-- The inverse image of a morphism of topoi is left exact. This is the `preservesFiniteLimits`
field, made available to instance search. -/
noncomputable instance preservesFiniteLimitsInverseImage :
    PreservesFiniteLimits f.inverseImage :=
  f.preservesFiniteLimits

/-- The direct image of a morphism of topoi preserves finite products, because it is a right
adjoint. No left exactness of `f⁻¹` is used: this is the only property of `f_*` that the
transport of algebraic structure below needs, and it is what puts the direct image on the same
footing as the inverse image. -/
@[sga "4 IV 3.1.2" "partial"]
noncomputable instance preservesFiniteProductsPushforward :
    PreservesFiniteProducts f.pushforward :=
  haveI := f.adj.rightAdjoint_preservesLimits
  inferInstance

end MorphismOfTopoi

/-! ## The direct image of a sheaf of rings and of a sheaf of modules -/

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback
open scoped Stacks.SheafLimitsProd

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  (O : Sheaf J RingCat.{ww})

/-- The direct image of a sheaf of rings along a morphism of topoi. Its underlying sheaf of
sets is the direct image of the underlying sheaf of sets of `O`.

This is `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` applied to `f.pushforward`: that
construction is stated for an arbitrary finite-product-preserving functor between categories
of sheaves of sets, with no adjointness assumed, so the direct image is an instance of it. -/
noncomputable def pushforwardRingSheaf : Sheaf K RingCat.{ww'} :=
  pullbackRingSheaf K f.pushforward O

/-- The underlying sheaf of sets of the direct-image sheaf of rings is, on the nose, the direct
image of the underlying sheaf of sets of `O`. -/
noncomputable def pushforwardRingSheafIso :
    Sheaf.ringSheaf (pushforwardRingSheaf f O) ≅ f.pushforward.obj (Sheaf.ringSheaf O) :=
  Iso.refl _

/-- **Stacks 03D1** for a single module: the direct image of a sheaf of `O`-modules is a sheaf
of modules over the direct-image sheaf of rings. -/
noncomputable def pushforwardModuleObj (G : SheafOfModules.{ww} O) :
    SheafOfModules.{ww'} (pushforwardRingSheaf f O) :=
  pullbackModuleObj K f.pushforward O G

/-- **Stacks 03D1.** Direct image along a morphism of topoi, as a functor from sheaves of
`O`-modules to sheaves of modules over the direct-image sheaf of rings. -/
noncomputable def pushforwardModuleFunctor :
    SheafOfModules.{ww} O ⥤ SheafOfModules.{ww'} (pushforwardRingSheaf f O) :=
  pullbackModuleFunctor K f.pushforward O

end Stacks.Sheaves.ToposPushforward

/-! ## The product comparison for a direct image -/

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback
open scoped Stacks.SheafLimitsProd

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

/-- The canonical comparison identifying the direct image of a binary product with the product
of the direct images. This is the isomorphism that Stacks 03D1 applies to the multiplication
map: it exists because `f_*` is a right adjoint, hence preserves finite products. -/
noncomputable def pushforwardProdIso (A B : Sheaf J (Type ww)) :
    f.pushforward.obj (A ⨯ B) ≅ f.pushforward.obj A ⨯ f.pushforward.obj B :=
  PreservesLimitPair.iso f.pushforward A B

lemma pushforwardProdIso_hom (A B : Sheaf J (Type ww)) :
    (pushforwardProdIso f A B).hom = Limits.prodComparison f.pushforward A B :=
  PreservesLimitPair.iso_hom _ _ _

@[simp]
lemma pushforwardProdIso_hom_fst (A B : Sheaf J (Type ww)) :
    (pushforwardProdIso f A B).hom ≫ Limits.prod.fst =
      f.pushforward.map Limits.prod.fst := by
  rw [pushforwardProdIso_hom, Limits.prodComparison_fst]

@[simp]
lemma pushforwardProdIso_hom_snd (A B : Sheaf J (Type ww)) :
    (pushforwardProdIso f A B).hom ≫ Limits.prod.snd =
      f.pushforward.map Limits.prod.snd := by
  rw [pushforwardProdIso_hom, Limits.prodComparison_snd]

/-- If `Φ` of a map out of `A ⨯ B` is the product comparison followed by `m`, then transporting
it through `Ψ` at a pair of elements agrees with transporting `m` along `Ψ` at that pair. -/
private lemma map_prodObjMk_eq (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww))
    [PreservesFiniteProducts Φ] (Ψ : Sheaf J (Type ww) ⥤ Type tt) [PreservesFiniteProducts Ψ]
    {A B C : Sheaf K (Type ww')}
    {g : A ⨯ B ⟶ C} {m : Φ.obj A ⨯ Φ.obj B ⟶ Φ.obj C}
    (h : Φ.map g = Limits.prodComparison Φ A B ≫ m) (x : Ψ.obj (Φ.obj A))
    (y : Ψ.obj (Φ.obj B)) :
    (Φ ⋙ Ψ).map g (CategoryTheory.Functor.prodObjMk (P := Φ ⋙ Ψ) (A := A) (B := B) x y) =
      Ψ.map m (CategoryTheory.Functor.prodObjMk (P := Ψ) (A := Φ.obj A) (B := Φ.obj B) x y) := by
  rw [Functor.comp_map, h, Ψ.map_comp_apply,
    CategoryTheory.Functor.map_prodComparison_apply, CategoryTheory.Functor.map_fst_prodObjMk,
    CategoryTheory.Functor.map_snd_prodObjMk]

/-- The analogue of `map_prodObjMk_eq` for maps out of the terminal object. -/
private lemma map_default_eq (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww))
    [PreservesFiniteProducts Φ] (Ψ : Sheaf J (Type ww) ⥤ Type tt) [PreservesFiniteProducts Ψ]
    {A : Sheaf K (Type ww')} {g : ⊤_ (Sheaf K (Type ww')) ⟶ A}
    {m : ⊤_ (Sheaf J (Type ww)) ⟶ Φ.obj A}
    (h : Φ.map g = Limits.terminalComparison Φ ≫ m) :
    (Φ ⋙ Ψ).map g default = Ψ.map m default := by
  rw [Functor.comp_map, h, Ψ.map_comp_apply]
  exact congrArg _ (Subsingleton.elim _ _)

end Stacks.Sheaves.ToposPushforward

/-! ## Direct images of sheaves of modules along a morphism of topoi -/

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback
open scoped Stacks.SheafLimitsProd

universe tt ww ww' vv uu vv' uu'

/-- The data asserting that direct image along a morphism of topoi carries modules over `O` to
modules over the direct-image ring. The natural isomorphisms identify the underlying ring and
module sheaves with their ordinary direct images, and the operation equations identify their
algebraic structures with the transported original structures. The displayed `action` is the
scalar multiplication of the resulting sheaf of modules.

This mirrors `Stacks.Sheaves.ToposPullback.PullbackModuleData` field for field, with
`f.inverseImage` replaced by `f.pushforward`. In particular the ring is a sheaf of rings over
the target site, built here rather than quoted from an identification with an externally
supplied direct-image ring functor. -/
structure PushforwardModuleData
    {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.HasSheafCompose (forget RingCat.{ww})]
    [K.HasSheafCompose (forget RingCat.{ww'})]
    [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
    [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
    (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
    (O : Sheaf J RingCat.{ww}) where
  /-- The direct-image sheaf of rings. -/
  ring : Sheaf K RingCat.{ww'}
  /-- Direct image of modules, functorial in the module. -/
  moduleFunctor : SheafOfModules.{ww} O ⥤ SheafOfModules.{ww'} ring
  /-- The underlying sheaf of the direct-image ring is the direct image of the underlying sheaf
  of the original ring. -/
  ringIso : Sheaf.ringSheaf ring ≅ f.pushforward.obj (Sheaf.ringSheaf O)
  /-- The underlying sheaf of a pushed-forward module is naturally its direct-image sheaf. -/
  moduleIso : moduleFunctor ⋙ Sheaf.moduleSheafFunctor ring ≅
    Sheaf.moduleSheafFunctor O ⋙ f.pushforward
  /-- The scalar multiplication map on each direct-image module. -/
  action (G : SheafOfModules.{ww} O) :
    Sheaf.ringSheaf ring ⨯ Sheaf.moduleSheaf ring (moduleFunctor.obj G) ⟶
      Sheaf.moduleSheaf ring (moduleFunctor.obj G)
  /-- The preceding map is the scalar multiplication belonging to the pushed-forward module. -/
  action_apply (G : SheafOfModules.{ww} O) (X : Dᵒᵖ)
      (p : (Sheaf.ringSheaf ring ⨯ Sheaf.moduleSheaf ring (moduleFunctor.obj G)).obj.obj X) :
      (action G).hom.app X p =
        let r : ring.obj.obj X :=
          (Limits.prod.fst :
            Sheaf.ringSheaf ring ⨯ Sheaf.moduleSheaf ring (moduleFunctor.obj G) ⟶
              Sheaf.ringSheaf ring).hom.app X p
        let m : (moduleFunctor.obj G).val.obj X :=
          (Limits.prod.snd :
            Sheaf.ringSheaf ring ⨯ Sheaf.moduleSheaf ring (moduleFunctor.obj G) ⟶
              Sheaf.moduleSheaf ring (moduleFunctor.obj G)).hom.app X p
        r • m
  /-- Ring addition is the direct image of the original addition. -/
  ringAdd_map :
    f.pushforward.map (Sheaf.ringAddHom O) =
      Limits.prodComparison f.pushforward (Sheaf.ringSheaf O) (Sheaf.ringSheaf O) ≫
        Limits.prod.map ringIso.inv ringIso.inv ≫ Sheaf.ringAddHom ring ≫ ringIso.hom
  /-- Ring multiplication is the direct image of the original multiplication. -/
  ringMul_map :
    f.pushforward.map (Sheaf.ringMulHom O) =
      Limits.prodComparison f.pushforward (Sheaf.ringSheaf O) (Sheaf.ringSheaf O) ≫
        Limits.prod.map ringIso.inv ringIso.inv ≫ Sheaf.ringMulHom ring ≫ ringIso.hom
  /-- Ring negation is the direct image of the original negation. -/
  ringNeg_map :
    f.pushforward.map (Sheaf.ringNegHom O) =
      ringIso.inv ≫ Sheaf.ringNegHom ring ≫ ringIso.hom
  /-- Ring zero is the direct image of the original zero. -/
  ringZero_map :
    f.pushforward.map (Sheaf.ringZeroHom O) =
      Limits.terminalComparison f.pushforward ≫ Sheaf.ringZeroHom ring ≫ ringIso.hom
  /-- Ring one is the direct image of the original one. -/
  ringOne_map :
    f.pushforward.map (Sheaf.ringOneHom O) =
      Limits.terminalComparison f.pushforward ≫ Sheaf.ringOneHom ring ≫ ringIso.hom
  /-- Module addition is the direct image of the original addition. -/
  moduleAdd_map (G : SheafOfModules.{ww} O) :
    f.pushforward.map (Sheaf.moduleAddHom O G) =
      Limits.prodComparison f.pushforward (Sheaf.moduleSheaf O G) (Sheaf.moduleSheaf O G) ≫
        Limits.prod.map (moduleIso.app G).inv (moduleIso.app G).inv ≫
          Sheaf.moduleAddHom ring (moduleFunctor.obj G) ≫ (moduleIso.app G).hom
  /-- Module negation is the direct image of the original negation. -/
  moduleNeg_map (G : SheafOfModules.{ww} O) :
    f.pushforward.map (Sheaf.moduleNegHom O G) =
      (moduleIso.app G).inv ≫ Sheaf.moduleNegHom ring (moduleFunctor.obj G) ≫
        (moduleIso.app G).hom
  /-- Module zero is the direct image of the original zero. -/
  moduleZero_map (G : SheafOfModules.{ww} O) :
    f.pushforward.map (Sheaf.moduleZeroHom O G) =
      Limits.terminalComparison f.pushforward ≫
        Sheaf.moduleZeroHom ring (moduleFunctor.obj G) ≫ (moduleIso.app G).hom
  /-- The action is the direct image of the original scalar multiplication, using the canonical
  binary-product comparison. This is the content of Stacks 03D1: `f_*` of the multiplication
  map `O × F ⟶ F`, read through the product comparison, is the action. -/
  action_map (G : SheafOfModules.{ww} O) :
    f.pushforward.map (Sheaf.moduleSMulHom O G) =
      Limits.prodComparison f.pushforward (Sheaf.ringSheaf O) (Sheaf.moduleSheaf O G) ≫
        Limits.prod.map ringIso.inv (moduleIso.app G).inv ≫ action G ≫ (moduleIso.app G).hom

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]

/-- **Stacks 03D1.** The direct image of a sheaf of `O`-modules under a morphism of topoi is
naturally a sheaf of modules over the direct-image ring, with scalar multiplication the direct
image of the original scalar multiplication read through the product comparison, and this
construction is functorial in the module. -/
@[stacks 03D1]
noncomputable def pushforwardModule
    (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
    (O : Sheaf J RingCat.{ww}) : PushforwardModuleData J K f O where
  ring := pushforwardRingSheaf f O
  moduleFunctor := pushforwardModuleFunctor f O
  ringIso := Iso.refl _
  moduleIso := Iso.refl _
  action := fun _ ↦ Sheaf.moduleSMulHom _ _
  action_apply := fun _ _ _ ↦ rfl
  ringAdd_map := ringAdd_map_aux K f.pushforward O
  ringMul_map := ringMul_map_aux K f.pushforward O
  ringNeg_map := ringNeg_map_aux K f.pushforward O
  ringZero_map := ringZero_map_aux K f.pushforward O
  ringOne_map := ringOne_map_aux K f.pushforward O
  moduleAdd_map := fun G ↦ moduleAdd_map_aux K f.pushforward O G
  moduleNeg_map := fun G ↦ moduleNeg_map_aux K f.pushforward O G
  moduleZero_map := fun G ↦ moduleZero_map_aux K f.pushforward O G
  action_map := fun G ↦ moduleSMul_map_aux K f.pushforward O G

end Stacks.Sheaves.ToposPushforward

/-! ## The action solved for, and scalar multiplication on sections -/

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback
open scoped Stacks.SheafLimitsProd

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  {O : Sheaf J RingCat.{ww}}

/-- Scalar multiplication on the underlying sheaf of sets of a sheaf of modules is, on
sections, the scalar multiplication of the module. -/
lemma moduleSMulHom_hom_app_apply (G : SheafOfModules.{ww} O) (X : Cᵒᵖ)
    (p : (Sheaf.ringSheaf O ⨯ Sheaf.moduleSheaf O G).obj.obj X) :
    (Sheaf.moduleSMulHom O G).hom.app X p =
      let r : O.obj.obj X :=
        (Limits.prod.fst : Sheaf.ringSheaf O ⨯ Sheaf.moduleSheaf O G ⟶
          Sheaf.ringSheaf O).hom.app X p
      let m : G.val.obj X :=
        (Limits.prod.snd : Sheaf.ringSheaf O ⨯ Sheaf.moduleSheaf O G ⟶
          Sheaf.moduleSheaf O G).hom.app X p
      r • m := rfl

/-- The action of a `PushforwardModuleData`, solved for: it is the product comparison followed
by the direct image of the original scalar multiplication, conjugated by the two identifying
isomorphisms. This is `action_map` rewritten in the direction that exhibits the action as
constructed from `f_*` of the multiplication map. -/
lemma PushforwardModuleData.action_eq (P : PushforwardModuleData J K f O)
    (G : SheafOfModules.{ww} O) :
    P.action G =
      Limits.prod.map P.ringIso.hom (P.moduleIso.app G).hom ≫
        (pushforwardProdIso f (Sheaf.ringSheaf O) (Sheaf.moduleSheaf O G)).inv ≫
          f.pushforward.map (Sheaf.moduleSMulHom O G) ≫ (P.moduleIso.app G).inv := by
  rw [P.action_map G, ← pushforwardProdIso_hom]
  simp only [← Category.assoc]
  simp

end Stacks.Sheaves.ToposPushforward

/-! ## Transport of the ring structure along a composite functor -/

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback
open scoped Stacks.SheafLimitsProd

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'})
  (Ψ : Sheaf J (Type ww) ⥤ Type tt) [PreservesFiniteProducts Ψ]

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})] in
/-- The product comparison of `Φ`, read on a pair of elements through a second
finite-product-preserving functor `Ψ` to types. -/
lemma map_prodComparison_prodObjMk (A B : Sheaf K (Type ww'))
    (x : Ψ.obj (Φ.obj A)) (y : Ψ.obj (Φ.obj B)) :
    Ψ.map (Limits.prodComparison Φ A B)
        (CategoryTheory.Functor.prodObjMk (P := Φ ⋙ Ψ) (A := A) (B := B) x y) =
      CategoryTheory.Functor.prodObjMk (P := Ψ) (A := Φ.obj A) (B := Φ.obj B) x y := by
  rw [CategoryTheory.Functor.map_prodComparison_apply,
    CategoryTheory.Functor.map_fst_prodObjMk, CategoryTheory.Functor.map_snd_prodObjMk]

/-- Transporting the ring addition in two steps, first along `Φ` and then along `Ψ`, gives the
same operation as transporting it in one step along `Φ ⋙ Ψ`. -/
lemma ringAddObj_comp (x y : Ψ.obj (Φ.obj (Sheaf.ringSheaf O))) :
    Sheaf.ringAddObj (pullbackRingSheaf J Φ O) Ψ x y = Sheaf.ringAddObj O (Φ ⋙ Ψ) x y :=
  (map_prodObjMk_eq Φ Ψ (ringAdd_map_aux' J Φ O) x y).symm

/-- Transporting the ring multiplication in two steps agrees with transporting it in one. -/
lemma ringMulObj_comp (x y : Ψ.obj (Φ.obj (Sheaf.ringSheaf O))) :
    Sheaf.ringMulObj (pullbackRingSheaf J Φ O) Ψ x y = Sheaf.ringMulObj O (Φ ⋙ Ψ) x y :=
  (map_prodObjMk_eq Φ Ψ (ringMul_map_aux' J Φ O) x y).symm

omit [PreservesFiniteProducts Ψ] in
/-- The inverse image of the negation map is the negation map of the inverse-image ring. -/
lemma ringNegHom_comp :
    Φ.map (Sheaf.ringNegHom O) = Sheaf.ringNegHom (pullbackRingSheaf J Φ O) :=
  (ringNeg_map_aux J Φ O).trans ((Category.id_comp _).trans (Category.comp_id _))

omit [PreservesFiniteProducts Ψ] in
/-- The inverse image of the zero section is the product comparison for the terminal object
followed by the zero section of the inverse-image ring. -/
lemma ringZeroHom_comp :
    Φ.map (Sheaf.ringZeroHom O) =
      Limits.terminalComparison Φ ≫ Sheaf.ringZeroHom (pullbackRingSheaf J Φ O) :=
  (ringZero_map_aux J Φ O).trans
    (congrArg (fun m ↦ Limits.terminalComparison Φ ≫ m)
      (Category.comp_id (Sheaf.ringZeroHom (pullbackRingSheaf J Φ O))))

omit [PreservesFiniteProducts Ψ] in
/-- The inverse image of the unit section is the product comparison for the terminal object
followed by the unit section of the inverse-image ring. -/
lemma ringOneHom_comp :
    Φ.map (Sheaf.ringOneHom O) =
      Limits.terminalComparison Φ ≫ Sheaf.ringOneHom (pullbackRingSheaf J Φ O) :=
  (ringOne_map_aux J Φ O).trans
    (congrArg (fun m ↦ Limits.terminalComparison Φ ≫ m)
      (Category.comp_id (Sheaf.ringOneHom (pullbackRingSheaf J Φ O))))

omit [PreservesFiniteProducts Ψ] in
/-- Transporting the ring negation in two steps agrees with transporting it in one. -/
lemma ringNegObj_comp (x : Ψ.obj (Φ.obj (Sheaf.ringSheaf O))) :
    Sheaf.ringNegObj (pullbackRingSheaf J Φ O) Ψ x = Sheaf.ringNegObj O (Φ ⋙ Ψ) x :=
  (congrArg (fun m ↦ Ψ.map m x) (ringNegHom_comp J Φ O)).symm

/-- Transporting the zero in two steps agrees with transporting it in one. -/
lemma ringZeroObj_comp :
    Sheaf.ringZeroObj (pullbackRingSheaf J Φ O) Ψ = Sheaf.ringZeroObj O (Φ ⋙ Ψ) :=
  (map_default_eq Φ Ψ (ringZeroHom_comp J Φ O)).symm

/-- Transporting the unit in two steps agrees with transporting it in one. -/
lemma ringOneObj_comp :
    Sheaf.ringOneObj (pullbackRingSheaf J Φ O) Ψ = Sheaf.ringOneObj O (Φ ⋙ Ψ) :=
  (map_default_eq Φ Ψ (ringOneHom_comp J Φ O)).symm

end Stacks.Sheaves.ToposPushforward

/-! ## The unit of the adjunction as a map of sheaves of rings -/

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Functor Opposite Stacks.Sheaves.ToposPullback
open scoped Stacks.SheafLimitsProd

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  (O : Sheaf K RingCat.{ww'})

/-- The inverse-image sheaf of rings, named for use alongside the direct image. -/
noncomputable abbrev inverseImageRingSheaf : Sheaf J RingCat.{ww} :=
  pullbackRingSheaf J f.inverseImage O

/-- The unit of the adjunction `f⁻¹ ⊣ f_*`, whiskered with the sections functor over a fixed
object of the target site. This is the natural transformation that the transported ring
structures are compared along. -/
noncomputable def unitSections (X : Dᵒᵖ) :
    Sheaf.sectionsFunctor K X ⟶
      (f.inverseImage ⋙ f.pushforward) ⋙ Sheaf.sectionsFunctor K X where
  app A := (Sheaf.sectionsFunctor K X).map (f.adj.unit.app A)
  naturality A B m := by
    dsimp
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg _ (f.adj.unit.naturality m)

/-- The unit `O ⟶ f_*f⁻¹O`, on sections over a fixed object, as a map of rings. The underlying
map of sets is the unit of `f⁻¹ ⊣ f_*` at the underlying sheaf of sets of `O`; that it respects
the operations is the comparison between transporting the ring structure in one step along
`f⁻¹ ⋙ f_*` and in two steps. -/
noncomputable def ringUnitApp (X : Dᵒᵖ) :
    O.obj.obj X ⟶ (pushforwardRingSheaf f (inverseImageRingSheaf f O)).obj.obj X :=
  letI := Sheaf.ringObjRing (inverseImageRingSheaf f O)
    (f.pushforward ⋙ Sheaf.sectionsFunctor K X)
  RingCat.ofHom
    { toFun := (Sheaf.sectionsFunctor K X).map (f.adj.unit.app (Sheaf.ringSheaf O))
      map_add' := fun x y ↦
        (congrArg ((Sheaf.sectionsFunctor K X).map (f.adj.unit.app (Sheaf.ringSheaf O)))
            (Sheaf.sectionsFunctor_map_ringAddHom O X x y).symm).trans
          ((Sheaf.ringAddObj_naturality O (unitSections f X) x y).trans
            (ringAddObj_comp J f.inverseImage O
              (f.pushforward ⋙ Sheaf.sectionsFunctor K X) _ _).symm)
      map_mul' := fun x y ↦
        (congrArg ((Sheaf.sectionsFunctor K X).map (f.adj.unit.app (Sheaf.ringSheaf O)))
            (Sheaf.sectionsFunctor_map_ringMulHom O X x y).symm).trans
          ((Sheaf.ringMulObj_naturality O (unitSections f X) x y).trans
            (ringMulObj_comp J f.inverseImage O
              (f.pushforward ⋙ Sheaf.sectionsFunctor K X) _ _).symm)
      map_zero' :=
        (congrArg ((Sheaf.sectionsFunctor K X).map (f.adj.unit.app (Sheaf.ringSheaf O)))
            (Sheaf.sectionsFunctor_map_ringZeroHom O X default).symm).trans
          ((Sheaf.ringZeroObj_naturality O (unitSections f X)).trans
            (ringZeroObj_comp J f.inverseImage O
              (f.pushforward ⋙ Sheaf.sectionsFunctor K X)).symm)
      map_one' :=
        (congrArg ((Sheaf.sectionsFunctor K X).map (f.adj.unit.app (Sheaf.ringSheaf O)))
            (Sheaf.sectionsFunctor_map_ringOneHom O X default).symm).trans
          ((Sheaf.ringOneObj_naturality O (unitSections f X)).trans
            (ringOneObj_comp J f.inverseImage O
              (f.pushforward ⋙ Sheaf.sectionsFunctor K X)).symm) }

/-- The unit `O ⟶ f_*f⁻¹O` as a morphism of sheaves of rings. This is the map along which
`f_*` of a sheaf of `f⁻¹O`-modules is restricted to an `O`-module in Stacks 03D3, and it is
supplied here directly from the adjunction, without the ring-level adjunction of Stacks
00YV. -/
noncomputable def ringUnit : O ⟶ pushforwardRingSheaf f (inverseImageRingSheaf f O) where
  hom :=
    { app := fun X ↦ ringUnitApp f O X
      naturality := fun X Y g ↦ by
        refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        exact NatTrans.naturality_apply (f.adj.unit.app (Sheaf.ringSheaf O)).hom g x }

end Stacks.Sheaves.ToposPushforward

/-! ## The direct image of sheaves of modules restricted along a map of sheaves of rings -/

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory

section PushforwardModulesAlong

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **The direct image of sheaves of modules along a morphism of topoi, restricted along a map of
sheaves of rings** `φ : O' ⟶ f_*O`: the Stacks 03D1 direct image `pushforwardModuleFunctor`,
followed by restriction of scalars along `φ`.

This is the one construction behind the direct images of sheaves of modules along morphisms of
ringed topoi: `AlgebraicGeometry.RingedToposHom.pushforwardModules` (at the structure map) and
`Stacks.Sheaves.RingedToposModules.directImageModules` (the right adjoint of Stacks 03D3, at the
unit `O ⟶ f_*f⁻¹O`) are defined as it. The two section universes are free and independent; no
commutativity is assumed. -/
noncomputable def pushforwardModulesAlong
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) (O : Sheaf J RingCat.{w})
    {O' : Sheaf K RingCat.{w'}} (φ : O' ⟶ pushforwardRingSheaf f O) :
    SheafOfModules.{w} O ⥤ SheafOfModules.{w'} O' :=
  pushforwardModuleFunctor f O ⋙ SheafOfModules.restrictScalars φ

end PushforwardModulesAlong

end Stacks.Sheaves.ToposPushforward
