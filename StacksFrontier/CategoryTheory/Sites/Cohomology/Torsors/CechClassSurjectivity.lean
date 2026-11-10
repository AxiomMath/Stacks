module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CochainsAlongAMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassInjectivity
import StacksCore.Tactic.StacksAttribute

/-!
# The torsor of a Čech cocycle

Let `(C, J)` be a site, let `U` be an object of `C` and let `𝒰 = {U_i → U}` be a covering
family of `U`. Let `0 → G → I → Q → 0` be a short exact sequence of abelian sheaves on `C`.
This file builds, from a Čech `1`-cocycle `z` of `𝒰` with values in `G` which becomes a Čech
coboundary in `I`, a torsor under `G|_U` on the localized site `(C/U, J.over U)` which is
trivial over every member of `𝒰` and whose transition cocycle is `z` on the nose. It is the
inverse map in the proof of Stacks 0A6G, built out of a short exact sequence rather than out
of an injective resolution.

The construction is the one in the source, read through the classification of torsors by first
cohomology. Restricting the inclusion `G → I` to `C/U` and taking its cokernel there gives a
short exact sequence `S'` on `C/U` with `S'.X₁ = G|_U`; the restricted inclusion is a
monomorphism because a short exact sequence is left exact on sections. A degree-zero Čech
cochain `b` of `I` with `d b = z` has local sections `b_i` over the members, and their images
in `S'.X₃` agree on the twofold fibre products — their difference there is the value of `z`,
which the projection kills — hence on every common refinement of two members, so the sheaf
condition for the covering sieve glues them to a section `q` of `S'.X₃` over the terminal
object of `C/U`. The torsor of local lifts of `q` through `S'`
(`Stacks.Cohomology.Torsors.fiberTorsor`, the torsor realizing the connecting map in Stacks
03AJ) then has `b_i` as a section over `U_i`, and the difference of two restricted `b_i` inside
it is exactly `z`, because the kernel sheaf acts on the lifts by addition of its image in the
middle sheaf.

## Main definitions

* `Stacks.Cohomology.Torsors.sliceComplex`: the short exact sequence on `C/U` restricted from a
  short exact sequence on `C`, with its cokernel formed on `C/U`.
* `Stacks.Cohomology.Torsors.quotSections`: the sections of its quotient term over the members
  of the covering family attached to a degree-zero Čech cochain of the middle sheaf.
* `Stacks.Cohomology.Torsors.quotGlobalSection`: the glued section of the quotient term, as a
  global section of an abelian sheaf on `C/U`.
* `Stacks.Cohomology.Torsors.cocycleTorsor` and `Stacks.Cohomology.Torsors.cocycleSection`: the
  torsor of a Čech cocycle and its sections over the members of the covering family.

## Main results

* `Stacks.Cohomology.Torsors.sliceComplex_shortExact`: the restricted complex is short exact.
* `Stacks.Cohomology.Torsors.exists_glued_quotSection`: the quotient sections glue.
* `Stacks.Cohomology.Torsors.transitionCochain_cocycleTorsor`: the transition cochain of the
  torsor of a cocycle is that cocycle.
* `Stacks.Cohomology.Torsors.cechClass_cocycleTorsor`: consequently its locally trivial
  isomorphism class has as Čech class the class of the cocycle — an inverse of
  `Stacks.Cohomology.Torsors.cechClass` wherever a cochain `b` exists.
* `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_cocycleTorsor`: under the bijection of
  Stacks 03AJ that class goes to the image of the glued section under the connecting map of the
  restricted short exact sequence.

## Implementation notes

The Čech complex of `𝒰` is formed with coefficients an abelian presheaf on `C` and with the
iterated fibre products taken in `C/U`, so a Čech cochain of `𝒰` with values in `G` is
literally a cochain with values in the restriction `G|_U`, and no comparison is needed between
the two. That is why the middle term of the short exact sequence on `C/U` has to be the
restriction of a sheaf on `C` rather than an injective object of `Sheaf (J.over U)`: a Čech
cochain of the latter is not a `Stacks.CechSite.cechCochain` at all. The cokernel, on the other
hand, is formed on `C/U`, which is what makes `Mono` of the restricted inclusion the only input
needed about restriction: exactness of restriction to a localized site is not available for
`AddCommGrpCat` coefficients.

`Stacks.Cohomology.Torsors.sliceComplex` is an `abbrev` rather than a `def` because its second
and third terms have to be interchangeable with their unfoldings, the sections of the restricted
middle sheaf over an object of `C/U` being the sections over its image in `C`.

What is *not* proved here is that a cochain `b` exists for every cocycle, which is the vanishing
of `Ȟ¹(𝒰, I)` for `I` injective
(`Stacks.CechSite.injective_sheaf_cechCohomology_isZero`, stated at the small-site universe
convention `Ab.{max a u v w}`), and hence the surjectivity of
`Stacks.Cohomology.Torsors.cechClass`; nor the identification of the connecting map used here
with the degree-one Čech-to-cohomology comparison of Stacks 03AX.

## References

* [Stacks Project, Tag 0A6G](https://stacks.math.columbia.edu/tag/0A6G)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03AI](https://stacks.math.columbia.edu/tag/03AI)
* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
* [Stacks Project, Tag 0B8R](https://stacks.math.columbia.edu/tag/0B8R), the same statement for
  an open covering of a topological space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe h t w v u

namespace Stacks.Cohomology.Torsors

open Stacks.CechSite

section Slice

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (U : C)
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf J AddCommGrpCat.{t})]
  (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)

omit [HasSheafify (J.over U) AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
include hS in
/-- The restriction of a monomorphism of abelian sheaves to a localized site is again a
monomorphism: its sections over an object of `C/U` are the sections over the image of that
object, where a short exact sequence is left exact. -/
lemma mono_overPullback_map_f :
    Mono ((J.overPullback AddCommGrpCat.{t} U).map S.f) :=
  Sheaf.mono_of_injective _ fun W ↦ (shortExact_sections_left_exact S hS (op W.unop.left)).1

/-- The short complex on a localized site obtained by restricting the inclusion of a short
exact sequence of abelian sheaves and taking its cokernel there. Its first term is the
restriction `S.X₁|_U`, so a torsor under it is a torsor under the restricted kernel sheaf. -/
abbrev sliceComplex : ShortComplex (Sheaf (J.over U) AddCommGrpCat.{t}) :=
  ShortComplex.mk _ (cokernel.π ((J.overPullback AddCommGrpCat.{t} U).map S.f))
    (cokernel.condition _)

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- The first term of `sliceComplex U S` is the restriction of `S.X₁` to `C/U`. -/
@[simp] lemma sliceComplex_X₁ : (sliceComplex U S).X₁ = S.X₁.over U := rfl

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- The second term of `sliceComplex U S` is the restriction of `S.X₂` to `C/U`. -/
@[simp] lemma sliceComplex_X₂ : (sliceComplex U S).X₂ = S.X₂.over U := rfl

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- The first map of `sliceComplex U S` is the restriction of `S.f` to `C/U`. -/
@[simp] lemma sliceComplex_f :
    (sliceComplex U S).f = (J.overPullback AddCommGrpCat.{t} U).map S.f := rfl

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
include hS in
/-- The restricted complex is short exact: its inclusion is a monomorphism by
`mono_overPullback_map_f` and its projection is the cokernel of that monomorphism. -/
lemma sliceComplex_shortExact : (sliceComplex U S).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := mono_overPullback_map_f U S hS
  epi_g := inferInstance

end Slice

section Glueing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U)
  [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf J AddCommGrpCat.{t})]
  (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))

/-- The sections of the quotient term of the restricted short exact sequence over the members
of the covering family, obtained by projecting the family of sections of the middle sheaf
underlying a degree-zero Čech cochain. -/
def quotSections (b : cechCochain E S.X₂.obj 0) (i : E.I₀) :
    (sliceComplex U S).X₃.obj.obj (op (Over.mk (E.f i))) :=
  (sliceComplex U S).g.hom.app (op (Over.mk (E.f i))) (cochainFam E S.X₂.obj b i)

omit [HasSheafify J AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- **The Čech cocycle is the difference of the two restrictions of the local sections of the
middle sheaf.** This is the hypothesis on the degree-zero cochain, read off at a pair of
indices through the degree-zero differential formula. -/
lemma map_cochainFam_sub (z : cocycles1 E S.X₁.obj) (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1))
    (k : Fin 2 → E.I₀) :
    S.f.hom.app (op ((∏ᶜ fun j ↦ Over.mk (E.f (k j)) : Over U).left))
        ((z : cechCochain E S.X₁.obj 1) k) =
      S.X₂.obj.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) (1 : Fin 2)).left.op
          (cochainFam E S.X₂.obj b (k 1)) -
        S.X₂.obj.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) (0 : Fin 2)).left.op
          (cochainFam E S.X₂.obj b (k 0)) := by
  have hd := cechDifferential_zero_famCochain E S.X₂.obj (cochainFam E S.X₂.obj b) k
  rw [famCochain_cochainFam] at hd
  rw [← hd, hb]
  rfl

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- **The quotient sections match on the twofold iterated fibre products.** The difference of
the two restrictions of the underlying sections of the middle sheaf is the value of the Čech
differential of the cochain, which by hypothesis comes from the kernel sheaf and is therefore
killed by the projection. -/
lemma map_quotSections_eq (z : cocycles1 E S.X₁.obj) (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1))
    (k : Fin 2 → E.I₀) :
    (sliceComplex U S).X₃.obj.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) (1 : Fin 2)).op
        (quotSections E S b (k 1)) =
      (sliceComplex U S).X₃.obj.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) (0 : Fin 2)).op
        (quotSections E S b (k 0)) := by
  have key2 := (congrArg ((sliceComplex U S).g.hom.app
      (op (∏ᶜ fun j ↦ Over.mk (E.f (k j)) : Over U)))
      (map_cochainFam_sub E S z b hb k).symm).trans
    (shortComplex_sections_zero (sliceComplex U S)
      (op (∏ᶜ fun j ↦ Over.mk (E.f (k j)) : Over U)) ((z : cechCochain E S.X₁.obj 1) k))
  have n := fun m : Fin 2 ↦ NatTrans.naturality_apply (sliceComplex U S).g.hom
    (Pi.π (fun j ↦ Over.mk (E.f (k j))) m).op (cochainFam E S.X₂.obj b (k m))
  exact (n 1).symm.trans ((sub_eq_zero.1 ((map_sub _ _ _).symm.trans key2)).trans (n 0))

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- **The quotient sections agree on every common refinement.** For any object of `C/U` and
any two morphisms from it to members of the covering family, the two restrictions of the
corresponding quotient sections agree: the pair of morphisms factors through the fibre product
of the two members, where `map_quotSections_eq` applies. -/
lemma map_quotSections_congr (z : cocycles1 E S.X₁.obj) (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1))
    {W : Over U} (k : Fin 2 → E.I₀) (a : W ⟶ Over.mk (E.f (k 0)))
    (a' : W ⟶ Over.mk (E.f (k 1))) :
    (sliceComplex U S).X₃.obj.map a.op (quotSections E S b (k 0)) =
      (sliceComplex U S).X₃.obj.map a'.op (quotSections E S b (k 1)) := by
  let u : W ⟶ (∏ᶜ fun m ↦ Over.mk (E.f (k m))) :=
    Pi.lift (fun m ↦ match m with | 0 => a | 1 => a')
  have h0 : u ≫ Pi.π (fun m ↦ Over.mk (E.f (k m))) 0 = a := Pi.lift_comp_π _ _
  have h1 : u ≫ Pi.π (fun m ↦ Over.mk (E.f (k m))) 1 = a' := Pi.lift_comp_π _ _
  rw [← h0, ← h1, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
    map_quotSections_eq E S z b hb k]

/-- The structure morphism of a member of the covering family, as a morphism to the terminal
object `𝟙 U` of `C/U`. -/
def memberToTerminal (i : E.I₀) : Over.mk (E.f i) ⟶ Over.mk (𝟙 U) :=
  Over.homMk (E.f i) (Category.comp_id _)

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
/-- **Glueing the quotient sections.** For a covering family, the sections of the quotient term
of the restricted short exact sequence over the members of the family agree on every common
refinement, so the sheaf condition for the covering sieve amalgamates them into a section over
the terminal object of `C/U`, that is, a section of the quotient over `U`. -/
lemma exists_glued_quotSection (hE : E.sieve₀ ∈ J U) (z : cocycles1 E S.X₁.obj)
    (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1)) :
    ∃ q : (sliceComplex U S).X₃.obj.obj (op (Over.mk (𝟙 U))), ∀ i : E.I₀,
      (sliceComplex U S).X₃.obj.map (memberToTerminal E i).op q = quotSections E S b i := by
  have hQ : Presieve.IsSheaf (J.over U)
      ((sliceComplex U S).X₃.obj ⋙ forget AddCommGrpCat.{t}) :=
    (isSheaf_iff_isSheaf_of_type (J.over U) _).1
      (Presheaf.isSheaf_comp_of_isSheaf (J.over U) _ (forget AddCommGrpCat)
        (sliceComplex U S).X₃.property)
  let T : Sieve (Over.mk (𝟙 U)) := (Sieve.overEquiv (Over.mk (𝟙 U))).symm E.sieve₀
  have hT : T ∈ (J.over U) (Over.mk (𝟙 U)) :=
    J.overEquiv_symm_mem_over (Over.mk (𝟙 U)) E.sieve₀ hE
  have hmem : ∀ {W : Over U} {f : W ⟶ Over.mk (𝟙 U)}, T.arrows f → E.sieve₀.arrows f.left :=
    fun hf ↦ hf
  have hex : ∀ {W : Over U} (f : W ⟶ Over.mk (𝟙 U)), E.sieve₀.arrows f.left →
      ∃ x : (sliceComplex U S).X₃.obj.obj (op W), ∀ (i : E.I₀) (a : W ⟶ Over.mk (E.f i)),
        (sliceComplex U S).X₃.obj.map a.op (quotSections E S b i) = x := by
    intro W f hf
    obtain ⟨i, ⟨a⟩⟩ := exists_hom_over_member E f hf
    refine ⟨(sliceComplex U S).X₃.obj.map a.op (quotSections E S b i), fun j c ↦ ?_⟩
    exact map_quotSections_congr E S z b hb ![j, i] c a
  let fam : Presieve.FamilyOfElements
      ((sliceComplex U S).X₃.obj ⋙ forget AddCommGrpCat.{t}) T.arrows :=
    fun _ f hf ↦ Classical.choose (hex f (hmem hf))
  have hfam : ∀ {W : Over U} (f : W ⟶ Over.mk (𝟙 U)) (hf : T.arrows f) (i : E.I₀)
      (a : W ⟶ Over.mk (E.f i)),
      (sliceComplex U S).X₃.obj.map a.op (quotSections E S b i) = fam f hf :=
    fun f hf ↦ Classical.choose_spec (hex f (hmem hf))
  have hcompat : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
    obtain ⟨i₁, ⟨a₁⟩⟩ := exists_hom_over_member E f₁ (hmem h₁)
    obtain ⟨i₂, ⟨a₂⟩⟩ := exists_hom_over_member E f₂ (hmem h₂)
    change (sliceComplex U S).X₃.obj.map g₁.op (fam f₁ h₁) =
      (sliceComplex U S).X₃.obj.map g₂.op (fam f₂ h₂)
    rw [← hfam f₁ h₁ i₁ a₁, ← hfam f₂ h₂ i₂ a₂, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    exact map_quotSections_congr E S z b hb ![i₁, i₂] (g₁ ≫ a₁) (g₂ ≫ a₂)
  obtain ⟨q, hq, -⟩ := hQ T hT fam hcompat
  refine ⟨q, fun i ↦ ?_⟩
  have hi : T.arrows (memberToTerminal E i) := Sieve.ofArrows_mk E.X E.f i
  refine (hq (memberToTerminal E i) hi).trans
    ((hfam (memberToTerminal E i) hi i (𝟙 _)).symm.trans ?_)
  rw [op_id, (sliceComplex U S).X₃.obj.map_id]
  rfl

end Glueing

section Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U)
  [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})]
  (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- The restrictions of a section over the terminal object of `C/U` form a compatible
family. -/
lemma terminalSection_natural (A : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{t})
    (q : A.obj (op (Over.mk (𝟙 U)))) {W W' : (Over U)ᵒᵖ} (f : W ⟶ W') :
    A.map f (A.map (Over.mkIdTerminal.from W.unop).op q) =
      A.map (Over.mkIdTerminal.from W'.unop).op q := by
  have h : (Over.mkIdTerminal.from W.unop).op ≫ f =
      (Over.mkIdTerminal.from W'.unop).op :=
    Quiver.Hom.unop_inj (Over.mkIdTerminal.hom_ext _ _)
  rw [← Functor.map_comp_apply, h]

/-- A section of an abelian sheaf on `C/U` over the terminal object, as a morphism from the
constant presheaf of integers: a section over the terminal object restricts to a compatible
family over every object. -/
def terminalSectionFamily (A : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{t})
    (q : A.obj (op (Over.mk (𝟙 U)))) :
    (Functor.const (Over U)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ A :=
  morphismOfSectionFamily A (fun W ↦ A.map (Over.mkIdTerminal.from W.unop).op q)
    (terminalSection_natural A q)

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- The value of `terminalSectionFamily` at an object: the restriction of the given section
along the unique morphism to the terminal object. -/
lemma terminalSectionFamily_app (A : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{t})
    (q : A.obj (op (Over.mk (𝟙 U)))) (W : (Over U)ᵒᵖ) :
    (terminalSectionFamily A q).app W ⟨1⟩ = A.map (Over.mkIdTerminal.from W.unop).op q :=
  morphismOfSectionFamily_one A _ (terminalSection_natural A q) W

/-- The section of the quotient term over `U` glued from the quotient sections of a
degree-zero Čech cochain, as a global section of the quotient sheaf on `C/U`. -/
def quotGlobalSection (hE : E.sieve₀ ∈ J U) (z : cocycles1 E S.X₁.obj)
    (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1)) :
    (Functor.const (Over U)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶
      (sliceComplex U S).X₃.obj :=
  terminalSectionFamily (sliceComplex U S).X₃.obj
    (Classical.choose (exists_glued_quotSection E S hE z b hb))

include hS in
/-- **The torsor of a Čech cocycle.** The torsor of local lifts of the glued quotient section
through the restricted short exact sequence, a torsor under the restriction `S.X₁|_U`. -/
@[sga "4½ Sommes_trig 1.3" "more general"]
def cocycleTorsor (hE : E.sieve₀ ∈ J U) (z : cocycles1 E S.X₁.obj)
    (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1)) :
    AbelianTorsor (S.X₁.over U) :=
  fiberTorsor (sliceComplex U S) (sliceComplex_shortExact U S hS)
    (quotGlobalSection E S hE z b hb)

include hS in
/-- **The torsor of a Čech cocycle has a section over every member of the covering family**:
the local section of the middle sheaf underlying the cochain is a lift of the glued quotient
section there, by the defining property of the glueing. -/
def cocycleSection (hE : E.sieve₀ ∈ J U) (z : cocycles1 E S.X₁.obj)
    (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1)) (i : E.I₀) :
    (cocycleTorsor E S hS hE z b hb).1.presheaf.obj (op (Over.mk (E.f i))) :=
  ⟨cochainFam E S.X₂.obj b i, by
    have hq := Classical.choose_spec (exists_glued_quotSection E S hE z b hb) i
    have h1 : (quotGlobalSection E S hE z b hb).app (op (Over.mk (E.f i))) ⟨1⟩ =
        (sliceComplex U S).X₃.obj.map (Over.mkIdTerminal.from (Over.mk (E.f i))).op
          (Classical.choose (exists_glued_quotSection E S hE z b hb)) :=
      terminalSectionFamily_app _ _ _
    rw [h1, Over.mkIdTerminal.hom_ext (Over.mkIdTerminal.from (Over.mk (E.f i)))
      (memberToTerminal E i), hq]
    rfl⟩

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
include hS in
/-- **The transition cocycle of the torsor of a Čech cocycle is that cocycle.** The difference
of the two restricted local sections inside the torsor of lifts is, by definition of the
action, the section of the kernel sheaf carrying one to the other, and that is the value of
the Čech cocycle by `map_cochainFam_sub`. -/
lemma transitionCochain_cocycleTorsor (hE : E.sieve₀ ∈ J U) (z : cocycles1 E S.X₁.obj)
    (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1)) :
    transitionCochain E S.X₁ (cocycleTorsor E S hS hE z b hb)
        (cocycleSection E S hS hE z b hb) =
      (z : cechCochain E S.X₁.obj 1) := by
  funext k
  refine torsorDifference_eq_of_act (S.X₁.over U) (cocycleTorsor E S hS hE z b hb)
    (op (∏ᶜ fun j ↦ Over.mk (E.f (k j)) : Over U)) _ _ ((z : cechCochain E S.X₁.obj 1) k) ?_
  refine Subtype.ext ?_
  change S.f.hom.app (op ((∏ᶜ fun j ↦ Over.mk (E.f (k j)) : Over U).left))
        ((z : cechCochain E S.X₁.obj 1) k) +
      S.X₂.obj.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) (0 : Fin 2)).left.op
        (cochainFam E S.X₂.obj b (k 0)) =
    S.X₂.obj.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) (1 : Fin 2)).left.op
      (cochainFam E S.X₂.obj b (k 1))
  rw [map_cochainFam_sub E S z b hb k, sub_add_cancel]

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
include hS in
/-- **The torsor of a Čech cocycle is locally trivial on the covering family**, because it has
a section over every member. -/
lemma isLocallyTrivialOn_cocycleTorsor (hE : E.sieve₀ ∈ J U) (z : cocycles1 E S.X₁.obj)
    (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1)) :
    IsLocallyTrivialOn E S.X₁ (Quotient.mk (torsorSetoid (S.X₁.over U))
      (cocycleTorsor E S hS hE z b hb)) :=
  ⟨cocycleTorsor E S hS hE z b hb, rfl, fun i ↦ ⟨cocycleSection E S hS hE z b hb i⟩⟩

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
include hS in
/-- **The Čech class of the torsor of a Čech cocycle is the class of that cocycle.** This is
the inverse map of Stacks 0A6G: a Čech class realized by a degree-zero cochain of the middle
sheaf of a short exact sequence comes from a locally trivial isomorphism class of torsors. -/
@[ega "IV 16.5.15" "partial"]
theorem cechClass_cocycleTorsor (hE : E.sieve₀ ∈ J U) (z : cocycles1 E S.X₁.obj)
    (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1)) :
    cechClass E S.X₁ ⟨Quotient.mk (torsorSetoid (S.X₁.over U))
        (cocycleTorsor E S hS hE z b hb),
      ⟨cocycleTorsor E S hS hE z b hb, rfl,
        fun i ↦ ⟨cocycleSection E S hS hE z b hb i⟩⟩⟩ = cls E S.X₁.obj z := by
  rw [cechClass_mk E S.X₁ (cocycleTorsor E S hS hE z b hb)
    (fun i ↦ ⟨cocycleSection E S hS hE z b hb i⟩) (cocycleSection E S hS hE z b hb)]
  exact congrArg (cls E S.X₁.obj)
    (Subtype.ext (transitionCochain_cocycleTorsor E S hS hE z b hb))

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{t})] in
include hS in
/-- **The first cohomology class of the torsor of a Čech cocycle.** Under the bijection of
Stacks 03AJ between isomorphism classes of torsors under `S.X₁|_U` and `H¹(C/U, S.X₁|_U)`, the
torsor of a Čech cocycle goes to the image of the glued quotient section under the connecting
map of the restricted short exact sequence. -/
theorem torsorIsoClassesEquivH1_cocycleTorsor (hE : E.sieve₀ ∈ J U)
    (z : cocycles1 E S.X₁.obj) (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1)) :
    torsorIsoClassesEquivH1 (S.X₁.over U)
        (Quotient.mk (torsorSetoid (S.X₁.over U)) (cocycleTorsor E S hS hE z b hb)) =
      (Abelian.Ext.mk₀
        (((sheafificationAdjunction (J.over U) AddCommGrpCat).homEquiv _ _).symm
          (quotGlobalSection E S hE z b hb))).comp
        (sliceComplex_shortExact U S hS).extClass (zero_add 1) :=
  torsorPushoutClass_fiber (sliceComplex U S) (sliceComplex_shortExact U S hS)
    (quotGlobalSection E S hE z b hb)

end Torsor

end Stacks.Cohomology.Torsors

end
