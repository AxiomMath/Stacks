module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Maps
public import StacksFrontier.CategoryTheory.Sites.Subtopos.Immersions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The essential image of the direct image of modules along a closed immersion of ringed topoi

Let `i : (Sh(C), O) → (Sh(D), O')` be a morphism of ringed topoi which is a closed immersion of
topoi and whose structure map `i^# : O' ⟶ i_*O` is surjective, and let `I ⊆ O'` be the kernel of
`i^#`. Stacks 08M3 asserts, among other things, that the essential image of
`i_* : Mod(O) ⥤ Mod(O')` consists exactly of the `O'`-modules `G` with `I·G = 0`.

This file proves the easy half of that characterization — an `O'`-module in the essential image is
annihilated by `I` — in a form that makes no use of either hypothesis on `i`, and then proves the
step of the converse that *does* use the closed-immersion hypothesis: every `i_*O`-module has, as a
sheaf of sets, the shape `i_*F`. The converse is *completed elsewhere in this library* and the
whole biconditional is proved unconditionally; the implementation notes say where, and which
declaration supplies each step.

The direct image of modules is `Stacks.Sheaves.ToposPushforward.pushforwardModuleFunctor`
(Stacks 03D1) followed by restriction of scalars along `i^#`, which is `pushforwardModules` below.

## Main definitions

* `Stacks.Sheaves.PushforwardEssentialImage.pushforwardModules`: the direct image on sheaves of
  modules determined by a morphism of topoi together with a map `O' ⟶ i_*O` of sheaves of rings,
  namely the Stacks 03D1 direct image followed by restriction of scalars along that map. This is
  the functor whose essential image Stacks 08M3 describes.

## Main results

* `Stacks.Sheaves.PushforwardEssentialImage.smul_eq_zero_of_essImage_restrictScalars`: a module
  in the essential image of any functor followed by restriction of scalars along `α` is annihilated
  by the sectionwise kernel of `α`. This is the content of the forward half of Stacks 08M3,
  isolated from the geometry: neither the closed-immersion hypothesis nor the surjectivity of the
  structure map plays any role in it.
* `Stacks.Sheaves.PushforwardEssentialImage.smul_eq_zero_of_essImage_pushforwardModules`: the
  forward half of the Stacks 08M3 characterization, read off from the previous result — if `G` is
  in the essential image of `pushforwardModules`, then every section of the kernel of `i^#`
  annihilates every section of `G` over the same object.
* `Stacks.Sheaves.PushforwardEssentialImage.closedComplement_moduleSheaf`: if the underlying sheaf
  of sets of a sheaf of rings `R` lies in the closed subtopos complementary to `U`, then so does
  the underlying sheaf of sets of every sheaf of `R`-modules. This is the Stacks 08M3 step
  "`G × U = {0} × U = U`".
* `Stacks.Sheaves.PushforwardEssentialImage.moduleSheaf_mem_essImage_pushforward`: for a closed
  immersion of topoi `i`, the underlying sheaf of sets of any sheaf of `i_*O`-modules lies in the
  essential image of `i_*` on sheaves of sets. This is the point at which the converse half of
  Stacks 08M3 uses the closed-immersion hypothesis, and it is the Stacks step "thus there exists a
  sheaf of sets `F` on `C` with `i_*F = G`".

## Implementation notes

The forward half is stated for an arbitrary source functor `Φ` and an arbitrary morphism `α` of
sheaves of rings, because that is all it needs: restriction of scalars along `α` sends a scalar
`a` to `α(a)`, so a section killed by `α` acts by zero. In particular the result carries no
`GrothendieckTopology.HasSheafCompose` hypotheses and no hypothesis on `i`, and it applies verbatim
to any direct-image-of-modules functor of the shape `Φ ⋙ restrictScalars α`, whichever
construction of the direct image is used. The specialization to the Stacks 03D1 direct image does
carry the `HasSheafCompose (forget RingCat)` instances, because
`Stacks.Sheaves.ToposPushforward.pushforwardModuleFunctor` carries them; that is a property of the
chosen construction of the direct image, not of the statement.

The hypothesis of `closedComplement_moduleSheaf` is used only through
`one_eq_zero_of_closedComplement_ringSheaf`: a subsheaf of the final object on which a sheaf of
rings becomes terminal is one on which `1 = 0`, hence on which every module over that sheaf of
rings vanishes. The argument is Yoneda-style for the ring, since `closedComplement U R` says
exactly that `U ⟶ R` has at most one element, and sectionwise for the module.

The converse half of the Stacks 08M3 characterization is not completed *in this file*, but it is
completed in this library, and the whole biconditional is proved unconditionally in two
independent proofs. The two inputs the converse might seem to need are handled as follows:

* the essential surjectivity of restriction of scalars along `i^#` onto the `I`-annihilated
  modules **exists, and is proved twice**: as
  `Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_of_smul_eq_zero` with the
  biconditional `essImage_restrictScalars_iff` beside it, in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RestrictScalarsEssentialImage.lean`, and again as
  `Deformation.ToposThickening.essImage_restrictScalars_of_smul_eq_zero`. No quotient sheaf of
  rings `O'/I` is constructed, and the `SheafOfModules.kerIdeal` shortcut is not used either.
  (Stacks 0930 is the *full-faithfulness* half, not this one.)
* the reconstruction of a sheaf of modules from an internal module object was **bypassed, not
  supplied**: no declaration of that shape exists in the library. Both completions avoid internal
  module objects entirely, by
  descending along the *unit* or the *counit* of `i^{-1} ⊣ i_*` instead:
  `Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModuleFunctor` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialImageDirect/ModuleDescent.lean`
  inverts the unit on the
  essential image, and
  `Stacks.Sheaves.PushforwardEssentialImage.essSurj_pushforwardModuleFunctor` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialSurjectivity.lean` restricts
  scalars along the inverse of the
  ring-level counit. So `CategoryTheory.Functor.FullyFaithful.moduleObj` is never needed, and the
  missing bridge out of `pullbackModuleObj`/`pushforwardModuleObj` is never on the path.

The resulting unconditional statements, both of which consume
`moduleSheaf_mem_essImage_pushforward` above as their closed-immersion input, are

* `Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_isClosedImmersion`
  of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialSurjectivity.lean`, which
  carries
  the Stacks 08M3 registration under the key `essential_image`, with
  `essImage_pushforwardModules_iff_of_epi_forget` beside it stating the same thing under Stacks'
  own surjectivity hypothesis (an epimorphism of the underlying sheaves of sets);
* `Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialImageDirect/Criterion.lean`,
  an independent proof.

The reduction that combines this file's forward half with the restriction-of-scalars half,
conditionally on essential surjectivity, is `essImage_pushforwardModules_iff_of_essSurj` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialImageReduction.lean`; the other
two clauses of Stacks 08M3 are
proved as well, exactness as `AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_exact`
and full faithfulness as
`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful`.

All five universes of the source are free and independent: `u`, `v` for the source site, `u'`, `v'`
for the target site, and `w` for the sections of the structure sheaves and of the modules. The
forward half is in fact more general, keeping the module universe independent of the ring universe;
the one place where they must agree is the Stacks 03D1 direct image, which is stated with a single
section universe per topos. The rings are `RingCat`-valued rather than `CommRingCat`-valued, which
is a generalization: commutativity is used nowhere below.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf

universe w w' v u v' u'

namespace Stacks.Sheaves.PushforwardEssentialImage

/-! ## Annihilation by the kernel: the forward half of Stacks 08M3 -/

section Annihilation

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  {R R' : Sheaf K RingCat.{w}} (α : R ⟶ R')

/-- A section of `R` killed by `α` annihilates every section of a sheaf of `R'`-modules with
scalars restricted along `α`: restriction of scalars makes `a` act as `α(a)`.

This is the mechanism behind the implication "`i_*F` is annihilated by the kernel of `i^#`" of
Stacks 08M3. -/
theorem smul_restrictScalars_eq_zero (M : SheafOfModules.{w'} R') (X : Dᵒᵖ)
    (a : R.obj.obj X) (ha : (α.hom.app X).hom a = 0)
    (m : ((SheafOfModules.restrictScalars.{w'} α).obj M).val.obj X) : a • m = 0 := by
  have h : a • m = (α.hom.app X).hom a • (show M.val.obj X from m) := rfl
  rw [h, ha, zero_smul]
  rfl

variable {α}

/-- Annihilation of all sections over an object by a fixed scalar is invariant under an
isomorphism of sheaves of modules. -/
theorem smul_eq_zero_of_iso {M G : SheafOfModules.{w'} R} (e : M ≅ G) (X : Dᵒᵖ)
    (a : R.obj.obj X) (h : ∀ x : M.val.obj X, a • x = 0) (m : G.val.obj X) : a • m = 0 := by
  have key : e.inv.val ≫ e.hom.val = 𝟙 G.val := by
    rw [← SheafOfModules.comp_val, e.inv_hom_id, SheafOfModules.id_val]
  have hm : (e.hom.val.app X) ((e.inv.val.app X) m) = m := by
    rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, key, PresheafOfModules.id_app,
      ModuleCat.id_apply]
  rw [← hm, ← _root_.map_smul, h, map_zero]

/-- **The forward half of Stacks 08M3.** A sheaf of `R`-modules in the essential image of any
functor into sheaves of `R'`-modules followed by restriction of scalars along `α : R ⟶ R'` is
annihilated by the sectionwise kernel of `α`.

Only the shape `Φ ⋙ SheafOfModules.restrictScalars α` of the functor is used: no property of `Φ`,
no hypothesis on the morphism of topoi underlying it, and no surjectivity of `α`. -/
theorem smul_eq_zero_of_essImage_restrictScalars {B : Type*} [Category B]
    (Φ : B ⥤ SheafOfModules.{w'} R') {G : SheafOfModules.{w'} R}
    (hG : (Φ ⋙ SheafOfModules.restrictScalars.{w'} α).essImage G) (X : Dᵒᵖ) (a : R.obj.obj X)
    (ha : a ∈ RingHom.ker (α.hom.app X).hom) (m : G.val.obj X) : a • m = 0 := by
  obtain ⟨b, ⟨e⟩⟩ := hG
  exact smul_eq_zero_of_iso e X a (smul_restrictScalars_eq_zero α (Φ.obj b) X a ha) m

end Annihilation

/-! ## The direct image on sheaves of modules of a morphism of ringed topoi -/

section Pushforward

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})]

open Stacks.Sheaves.ToposPushforward

/-- The direct image on sheaves of modules determined by a morphism of topoi `f` together with a
morphism of sheaves of rings `fSharp : O' ⟶ f_*O`: the Stacks 03D1 direct image, followed by
restriction of scalars along `fSharp`.

This is the functor `i_* : Mod(O) ⥤ Mod(O')` of Stacks 08M3; the morphism `fSharp` is the
structure map of the morphism of ringed topoi. It is
`Stacks.Sheaves.ToposPushforward.pushforwardModulesAlong` at a single section universe. -/
@[sga "4 IV 13.2.1"]
noncomputable abbrev pushforwardModules
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))) (O : Sheaf J RingCat.{w})
    {O' : Sheaf K RingCat.{w}} (fSharp : O' ⟶ pushforwardRingSheaf f O) :
    SheafOfModules.{w} O ⥤ SheafOfModules.{w} O' :=
  pushforwardModulesAlong f O fSharp

/-- **The forward half of Stacks 08M3.** If a sheaf of `O'`-modules `G` is in the essential image
of the direct image `i_* : Mod(O) ⥤ Mod(O')`, then every section of the kernel ideal of the
structure map `i^#` annihilates every section of `G` over the same object of the site.

This is the Stacks step "it is clear that `i_*F` is annihilated by `I` for any `O`-module `F`".
Neither the closed-immersion hypothesis on `i` nor the surjectivity of `i^#` is needed. -/
theorem smul_eq_zero_of_essImage_pushforwardModules
    {f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))} {O : Sheaf J RingCat.{w}}
    {O' : Sheaf K RingCat.{w}} (fSharp : O' ⟶ pushforwardRingSheaf f O)
    {G : SheafOfModules.{w} O'} (hG : (pushforwardModules f O fSharp).essImage G) (X : Dᵒᵖ)
    (a : O'.obj.obj X) (ha : a ∈ RingHom.ker (fSharp.hom.app X).hom) (m : G.val.obj X) :
    a • m = 0 :=
  smul_eq_zero_of_essImage_restrictScalars _ hG X a ha m

end Pushforward

/-! ## Modules over a sheaf of rings that is terminal on a subsheaf of the final object -/

section ClosedComplement

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}

/-- If the projection `U ⨯ A ⟶ U` is an isomorphism, then `A` has at most one section over `U`:
the two lifts `U ⟶ U ⨯ A` along the projection determined by two such sections agree, because an
isomorphism is a monomorphism.

For `U` a subsheaf of the final object this says that `A` becomes terminal on the closed subtopos
complementary to `U`. -/
theorem subsingleton_hom_of_closedComplement {U A : Sheaf K (Type w)}
    (h : closedComplement U A) (z z' : U ⟶ A) : z = z' := by
  have : IsIso (prod.fst : U ⨯ A ⟶ U) := h
  have key : (prod.lift (𝟙 U) z : U ⟶ U ⨯ A) = prod.lift (𝟙 U) z' :=
    (cancel_mono (prod.fst : U ⨯ A ⟶ U)).mp (by simp)
  simpa using key =≫ prod.snd

variable [K.HasSheafCompose (forget RingCat.{w})] {U : Sheaf K (Type w)} {R : Sheaf K RingCat.{w}}

/-- A sheaf of rings whose underlying sheaf of sets lies in the closed subtopos complementary to
`U` has `1 = 0` over every object of the site carrying a section of `U`: the unit and the zero are
two sections of the ring over `U`, hence equal. -/
theorem one_eq_zero_of_closedComplement_ringSheaf (h : closedComplement U (Sheaf.ringSheaf R))
    (X : Dᵒᵖ) (u : (sectionsFunctor K X).obj U) : (1 : R.obj.obj X) = 0 := by
  have key := subsingleton_hom_of_closedComplement h
    (terminal.from U ≫ Sheaf.ringOneHom R) (terminal.from U ≫ Sheaf.ringZeroHom R)
  have h2 := congrArg (fun m : U ⟶ Sheaf.ringSheaf R ↦ (sectionsFunctor K X).map m u) key
  simp only [Functor.map_comp_apply, Functor.map_terminalFrom_apply,
    sectionsFunctor_map_ringOneHom, sectionsFunctor_map_ringZeroHom] at h2
  exact h2

/-- **The Stacks 08M3 step `G × U = {0} × U = U`.** If the underlying sheaf of sets of a sheaf of
rings `R` lies in the closed subtopos complementary to `U`, then so does the underlying sheaf of
sets of every sheaf of `R`-modules: over any object carrying a section of `U` the ring has `1 = 0`,
hence the module vanishes, so the zero section is a two-sided inverse to the projection. -/
theorem closedComplement_moduleSheaf (h : closedComplement U (Sheaf.ringSheaf R))
    (M : SheafOfModules.{w} R) : closedComplement U (Sheaf.moduleSheaf R M) := by
  have key : (prod.snd : U ⨯ Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R M) =
      prod.fst ≫ terminal.from U ≫ Sheaf.moduleZeroHom R M := by
    refine hom_ext_sections (fun X s ↦ ?_)
    have h1 : (1 : (sectionsFunctor K X).obj (Sheaf.ringSheaf R)) = 0 :=
      one_eq_zero_of_closedComplement_ringSheaf h X ((sectionsFunctor K X).map prod.fst s)
    have h2 : ((sectionsFunctor K X).map
        (prod.snd : U ⨯ Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R M) s) = 0 := by
      have h3 := (one_smul ((sectionsFunctor K X).obj (Sheaf.ringSheaf R))
        ((sectionsFunctor K X).map
          (prod.snd : U ⨯ Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R M) s)).symm
      rwa [h1, zero_smul] at h3
    rw [h2]
    simp only [Functor.map_comp_apply, Functor.map_terminalFrom_apply,
      sectionsFunctor_map_moduleZeroHom]
  refine ⟨⟨prod.lift (𝟙 U) (terminal.from U ≫ Sheaf.moduleZeroHom R M), ?_, by simp⟩⟩
  refine prod.hom_ext ?_ ?_
  · simp
  · simpa using key.symm

end ClosedComplement

/-! ## Descent of the underlying sheaf of sets along a closed immersion -/

section ClosedImmersion

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]

open Stacks.Sheaves.ToposPushforward

/-- **The Stacks 08M3 step "there exists a sheaf of sets `F` on `C` with `i_*F = G`".** Let `i` be
a closed immersion of topoi and `O` a sheaf of rings on the source. Then the underlying sheaf of
sets of any sheaf of modules over the direct image `i_*O` is in the essential image of `i_*` on
sheaves of sets.

Indeed `i_*O` is itself in that essential image, which by the closed-immersion hypothesis is the
closed subtopos complementary to some subsheaf `U` of the final object, and
`closedComplement_moduleSheaf` propagates membership from the sheaf of rings to its modules. Only
the closed-subtopos half of the hypothesis is used: neither the fact that `i` is an embedding nor
any surjectivity of a structure map enters. -/
theorem moduleSheaf_mem_essImage_pushforward
    {f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))}
    (hf : MorphismOfTopoi.IsClosedImmersion f) {O : Sheaf J RingCat.{w}}
    (M : SheafOfModules.{w} (pushforwardRingSheaf f O)) :
    f.pushforward.essImage (Sheaf.moduleSheaf (pushforwardRingSheaf f O) M) := by
  obtain ⟨U, _, hU⟩ := hf.2
  have hU' : closedComplement U = f.pushforward.essImage := hU
  have hring : closedComplement U (Sheaf.ringSheaf (pushforwardRingSheaf f O)) :=
    hU' ▸ ⟨Sheaf.ringSheaf O, ⟨Iso.refl _⟩⟩
  exact hU' ▸ closedComplement_moduleSheaf hring M

end ClosedImmersion

end Stacks.Sheaves.PushforwardEssentialImage
