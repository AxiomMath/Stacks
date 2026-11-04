module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorIdempotentStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorRankVanishing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.FlatFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseInvertibleDescent
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.FreeRetract
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.StalkAmbient
import StacksCore.Tactic.StacksAttribute

/-!
# The determinant of a flat sheaf of modules of finite presentation is of finite presentation

Let `(Y, 𝒪_Y)` be a ringed space and `F` a flat sheaf of `𝒪_Y`-modules of finite presentation.
This file proves that `det(F)` is of finite presentation, which is the last hypothesis of
[Stacks, Tag 0FJN] that the source does not assume.

The route is the rank-idempotent one, not the source's. Around every point Stacks 08BL gives an
open `U` on which `F|_U` is a retract of a finite free sheaf of modules, hence
(`Stacks.AssociatedSheaf.exists_associatedSheaf_iso_of_retract_free`) is the sheaf `ℱ_M`
associated to a finite projective `𝒪_Y(U)`-module `M` on the restricted ringed space. Each
degreewise exterior annihilator `annₙ(F|_U)` is then cut out of `⋀ⁿ(F|_U)` by multiplication by
the rank-`n` idempotent `eₙ` of `M`: the germ of `eₙ` at a point of `U` is the rank-`n` idempotent
of the stalk of `F` there
(`Stacks.AssociatedSheaf.germ_rankIdempotent_eq_rankIdempotent_stalk_of_restrict`), and the two
retract conditions of the argument are stalk-local
(`SheafOfModules.TensorExteriorSymmetricAlgebras.forall_smul_mem_exteriorAnnihilator_over` and
`forall_smul_eq_self_of_mem_exteriorAnnihilator_over`). Only finitely many degrees survive,
because only finitely many rank strata of `M` are nonempty
(`ProjectiveDeterminant.exists_finset_rankLocus_cover`) and outside them `eₙ = 0`, which makes
`annₙ(F|_U)` a zero object. So `det(F)|_U` is a finite coproduct of retracts of finite free
sheaves of modules, hence finitely presented, and finite presentation is local.

## Main results

* `SheafOfModules.TensorExteriorSymmetricAlgebras`
  `.exists_isFinite_presentation_determinant_over_of_isFlat`: **the determinant is finitely
  presented on a neighbourhood of every point.**
* `SheafOfModules.TensorExteriorSymmetricAlgebras.isFinitePresentation_determinant_of_isFlat`:
  **the determinant of a flat sheaf of modules of finite presentation on a ringed space is of
  finite presentation.**
* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinant_isInvertible_of_isFlat`: **Tag
  0FJN**, with flatness and finite presentation of `F` as its only hypotheses and nothing assumed
  about `det(F)`.
* `ProjectiveDeterminant.rankIdempotent_congr_instance`, with
  `ProjectiveDeterminant.finite_of_instance_eq` and
  `ProjectiveDeterminant.projective_of_instance_eq`: the rank idempotent and its two finiteness
  hypotheses transported along an *equality* of `Module` instances.

## Implementation notes

**Why the three transports along an equality of `Module` instances.** The stalk of a sheaf of
modules carries two `Module` instances which are equal but not definitionally so under the module
system — Mathlib's
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier` and this
repository's `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, whose equality is
`Stacks.SheafOfModules.stalkModule_eq`. Which of the two instance search finds depends on whether
the ringed space is a variable or a concrete term: at a variable `Osharp` the unification problem
`?Y.presheaf =?= Osharp.obj` puts a metavariable under a projection and the repository's instance
is not retrieved, whereas at `Y.sheaf` for a concrete `Y` it is. So the statements of
`ExteriorAnnihilatorIdempotentStalk`, which are made at a variable, and those of
`StalkAmbient`, which are made at a ringed space, are at the two different instances, and
closing the gap by a definitional-equality check is not possible: unfolding one into the other
passes through `CategoryTheory.Limits.getColimitCocone`, whose definition the module system does
not expose. `rankIdempotent_congr_instance` crosses it instead, by substituting the equality —
which works because its two instances are *variables*, so `subst` applies and the two finiteness
hypotheses then agree by proof irrelevance.

For the same reason the hypotheses `hfin`, `hproj` and `hidem` below are stated with Mathlib's
instance written out: left to instance search at the concrete ringed space they would come out at
the repository's and not match what
`exists_isFinite_presentation_determinant_over_of_germ_eq_rankIdempotent` asks for.

**The open the rank idempotent is a section over.** `M` is a module over
`(Y.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)`, the global sections of the restricted
ringed space, which is `𝒪_Y` evaluated at the image of `⊤` rather than at `U`. The two opens are
equal (`TopologicalSpace.Opens.isOpenEmbedding_obj_top`) but not syntactically, and the type of
`M` depends on the first, so the idempotent is carried to a section over `U` by the restriction
map along `eqToHom`; a germ is unchanged by that (`TopCat.Presheaf.germ_res_apply`).

**Sheafification on the slice sites.** The site of opens and each of its slices are essentially
small, so `CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` supply the two
instances the locality of finite presentation and the determinant over an open ask for. They are
not global instances, hence the `letI`s.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 08BL](https://stacks.math.columbia.edu/tag/08BL)
* [Stacks Project, Section 0FJ9](https://stacks.math.columbia.edu/tag/0FJ9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
  TopologicalSpace
open Stacks.AssociatedSheaf (hasModuleSheafify moduleSheafifyWEqualsLocallyBijective)

universe u

namespace ProjectiveDeterminant

/-! ### Transport along an equality of module structures -/

/-- Finiteness transported along an equality of `Module` instances. -/
theorem finite_of_instance_eq {R M : Type u} [CommRing R] [AddCommGroup M]
    {i₁ i₂ : Module R M} (h : i₁ = i₂) (hf : @Module.Finite R M _ _ i₁) :
    @Module.Finite R M _ _ i₂ := h ▸ hf

/-- Projectivity transported along an equality of `Module` instances. -/
theorem projective_of_instance_eq {R M : Type u} [CommRing R] [AddCommGroup M]
    {i₁ i₂ : Module R M} (h : i₁ = i₂) (hf : @Module.Projective R _ M _ i₁) :
    @Module.Projective R _ M _ i₂ := h ▸ hf

/-- **The rank idempotent transported along an equality of `Module` instances.** Two `Module`
structures on the same module which are equal — such as the two structures on the stalk of a
sheaf of modules compared by `Stacks.SheafOfModules.stalkModule_eq` — give the same rank
idempotent.

The instances are variables, so the equality may be substituted; the two pairs of finiteness and
projectivity hypotheses then agree by proof irrelevance. This is what crosses between the two
instances where a definitional-equality check cannot: see the implementation notes of this
file. -/
theorem rankIdempotent_congr_instance {R M : Type u} [CommRing R] [AddCommGroup M]
    {i₁ i₂ : Module R M} (h : i₁ = i₂)
    (f₁ : @Module.Finite R M _ _ i₁) (p₁ : @Module.Projective R _ M _ i₁)
    (f₂ : @Module.Finite R M _ _ i₂) (p₂ : @Module.Projective R _ M _ i₂) (n : ℕ) :
    @rankIdempotent R _ M _ i₁ f₁ p₁ n = @rankIdempotent R _ M _ i₂ f₂ p₂ n := by
  subst h
  rfl

end ProjectiveDeterminant

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

/-! ### The determinant on a trivialising open -/

/-- **The determinant of a flat sheaf of modules of finite presentation is finitely presented on
a neighbourhood of every point.**

Stacks 08BL gives an open `U` around the point on which `G|_U` is a retract of a finite free
sheaf of modules, and `Stacks.AssociatedSheaf.exists_associatedSheaf_iso_of_retract_free` turns
that retract into a finite projective `𝒪_Y(U)`-module `M` with `G|_U ≅ ℱ_M`. The compatible
family of scalars is the rank-`n` idempotent of `M`, restricted from `U`
(`Stacks.SheafOfModules.terminalSection`); its germ at a point of `U` is the rank-`n` idempotent
of the stalk of `G` there, which is
`Stacks.AssociatedSheaf.germ_rankIdempotent_eq_rankIdempotent_stalk_of_restrict`, and that is
exactly the hypothesis of
`exists_isFinite_presentation_determinant_over_of_germ_eq_rankIdempotent`. The finitely many
degrees that survive are the ones whose rank stratum of `M` is nonempty; outside them the
idempotent vanishes, and a submodule on which a vanishing scalar acts as the identity is a zero
object (`Stacks.SheafOfModules.isZero_toSheafOfModules_of_smul_eq_self`).

The stalkwise finiteness and projectivity are the ones Tag 0FJN's own hypotheses give: the
stalks of `G` are of finite presentation because `G` is, and projective because they are flat
and of finite presentation. -/
theorem exists_isFinite_presentation_determinant_over_of_isFlat {Y : RingedSpace.{u, u}}
    (G : SheafOfModules.{u} (structureSheafRing Y)) [G.IsFinitePresentation]
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier) G)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) G)
    (x : Y.carrier) :
    ∃ U : Opens Y.carrier, x ∈ U ∧
      ∃ p : ((A.determinant).over U).Presentation, p.IsFinite := by
  obtain ⟨U, hxU, k, ⟨ρ⟩⟩ :=
    Stacks.SheafOfModules.isLocallyFiniteFreeSummand_of_isFlat_of_isFinitePresentation G hflat x
  obtain ⟨M, _, _, ⟨e⟩⟩ :=
    Stacks.AssociatedSheaf.exists_associatedSheaf_iso_of_retract_free U G (ULift.{u} (Fin k)) ρ
  let : HasSheafify ((Opens.grothendieckTopology (Y.carrier : Type u)).over U)
      AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  let : ((Opens.grothendieckTopology (Y.carrier : Type u)).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  refine ⟨U, hxU, ?_⟩
  have hUtop : (TopCat.Presheaf.imF U).obj ⊤ = U := Opens.isOpenEmbedding_obj_top U
  let Os : Sheaf (Opens.grothendieckTopology (Y.carrier : Type u)) CommRingCat.{u} :=
    ⟨Y.presheaf, Y.IsSheaf⟩
  let a : ℕ → ToType (Y.presheaf.obj (op U)) := fun n =>
    (Y.presheaf.map (eqToHom hUtop.symm).op).hom
      (ProjectiveDeterminant.rankIdempotent
        (R := (Y.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) (M := M) n)
  let B : TensorExteriorSymmetricAlgebras (Osharp := Os.over U)
      ((Opens.grothendieckTopology (Y.carrier : Type u)).over U) (G.over U) :=
    SheafOfModules.algebras (Osharp := Os.over U)
      ((Opens.grothendieckTopology (Y.carrier : Type u)).over U) (G.over U)
  let B' : TensorExteriorSymmetricAlgebras (Osharp := Os.over U)
      ((Opens.grothendieckTopology (Y.carrier : Type u)).over U)
      (_root_.SheafOfModules.free
        (R := toRingCat ((Opens.grothendieckTopology (Y.carrier : Type u)).over U) (Os.over U))
        (ULift.{u} (Fin k))) :=
    SheafOfModules.algebras (Osharp := Os.over U)
      ((Opens.grothendieckTopology (Y.carrier : Type u)).over U) _
  let ρ' : Retract (G.over U) (_root_.SheafOfModules.free
      (R := toRingCat ((Opens.grothendieckTopology (Y.carrier : Type u)).over U) (Os.over U))
      (ULift.{u} (Fin k))) := ρ
  let f : ℕ → ((toRingCat ((Opens.grothendieckTopology (Y.carrier : Type u)).over U)
      (Os.over U)).obj ⋙ CategoryTheory.forget RingCat).sections := fun n =>
    Stacks.SheafOfModules.terminalSection
      (toRingCat ((Opens.grothendieckTopology (Y.carrier : Type u)).over U) (Os.over U))
      (Over.mk (𝟙 U)) Over.mkIdTerminal (a n)
  obtain ⟨sdeg, hsdeg⟩ := ProjectiveDeterminant.exists_finset_rankLocus_cover
    (R := (Y.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) (M := M)
  have hfin : ∀ (V : (Over U)ᵒᵖ) (y : (Y.carrier : Type u)), y ∈ (unop V).left →
      @Module.Finite (ToType (TopCat.Presheaf.stalk Os.obj y))
        (ToType (TopCat.Presheaf.stalk G.val.presheaf y)) _ _
        (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := Os.obj) G.val y) := by
    intro V y _
    let instG := Stacks.SheafOfModules.stalkModule G y
    have : @Module.FinitePresentation _ _ _ _ instG :=
      Stacks.SheafOfModules.finitePresentation_stalk G y
    exact (inferInstance : @Module.Finite _ _ _ _ instG)
  have hproj : ∀ (V : (Over U)ᵒᵖ) (y : (Y.carrier : Type u)), y ∈ (unop V).left →
      @Module.Projective (ToType (TopCat.Presheaf.stalk Os.obj y)) _
        (ToType (TopCat.Presheaf.stalk G.val.presheaf y)) _
        (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := Os.obj) G.val y) := fun _ y _ =>
    projective_stalk y ((AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat Y.sheaf G).mp
      hflat y)
  have hidem : ∀ (n : ℕ) (V : (Over U)ᵒᵖ) (y : (Y.carrier : Type u)) (hy : y ∈ (unop V).left),
      TopCat.Presheaf.germ Os.obj (unop V).left y hy ((f n).val V) =
        @ProjectiveDeterminant.rankIdempotent (ToType (TopCat.Presheaf.stalk Os.obj y)) _
          (ToType (TopCat.Presheaf.stalk G.val.presheaf y)) _
          (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := Os.obj) G.val y)
          (hfin V y hy) (hproj V y hy) n := by
    intro n V y hy
    have hy' : y ∈ U := (unop V).hom.le hy
    have heq := Stacks.SheafOfModules.stalkModule_eq Y (Stacks.AssociatedSheaf.valOf G) y
    have hfinT := ProjectiveDeterminant.finite_of_instance_eq heq.symm (hfin V y hy)
    have hprojT := ProjectiveDeterminant.projective_of_instance_eq heq.symm (hproj V y hy)
    have hfV : (f n).val V = (Os.obj.map ((unop V).hom).op).hom (a n) := by
      rw [show (f n).val V =
          (Os.obj.map ((Over.mkIdTerminal.from (unop V)).left).op).hom (a n) from rfl,
        Subsingleton.elim (Over.mkIdTerminal.from (unop V)).left (unop V).hom]
    have h1 : TopCat.Presheaf.germ Os.obj (unop V).left y hy ((f n).val V) =
        TopCat.Presheaf.germ Os.obj U y hy' (a n) := by
      rw [hfV]
      exact TopCat.Presheaf.germ_res_apply Os.obj (unop V).hom y hy (a n)
    have h2 : TopCat.Presheaf.germ Os.obj U y hy' (a n) =
        Y.presheaf.germ ((TopCat.Presheaf.imF U).obj ⊤) y
          ⟨(⟨y, hy'⟩ : (Y.restrict U.isOpenEmbedding).carrier), trivial, rfl⟩
          (ProjectiveDeterminant.rankIdempotent
            (R := (Y.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) (M := M) n) :=
      TopCat.Presheaf.germ_res_apply Y.presheaf (eqToHom hUtop.symm) y hy' _
    exact (h1.trans h2).trans
      ((Stacks.AssociatedSheaf.germ_rankIdempotent_eq_rankIdempotent_stalk_of_restrict U G hy'
        M e n hfinT hprojT).trans
        (ProjectiveDeterminant.rankIdempotent_congr_instance heq hfinT hprojT (hfin V y hy)
          (hproj V y hy) n))
  refine exists_isFinite_presentation_determinant_over_of_germ_eq_rankIdempotent A U B f
    hfin hproj hidem B' ρ' sdeg fun n hn => ?_
  have ha0 : a n = 0 := by
    dsimp only [a]
    rw [ProjectiveDeterminant.rankIdempotent_eq_zero_of_not_mem_finset_cover hsdeg hn]
    exact map_zero (Y.presheaf.map (eqToHom hUtop.symm).op).hom
  exact Stacks.SheafOfModules.isZero_toSheafOfModules_of_smul_eq_self _
    (B.exteriorAnnihilator n) (f n)
    (forall_smul_eq_self_of_mem_exteriorAnnihilator_over A U B f hfin hproj hidem n)
    (fun V => Stacks.SheafOfModules.terminalSection_val_eq_zero _ (Over.mk (𝟙 U))
      Over.mkIdTerminal ha0 V)

/-! ### The conclusion -/

/-- **The determinant of a flat sheaf of modules of finite presentation on a ringed space is of
finite presentation.** This is the hypothesis `hdet` of
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant_isInvertible_of_isFlat`, and it is
the last hypothesis of [Stacks, Tag 0FJN] that the source does not assume.

Finite presentation is local
(`Stacks.SheafOfModules.isFinitePresentation_of_coversTop`), and
`exists_isFinite_presentation_determinant_over_of_isFlat` presents the determinant finitely on a
neighbourhood of every point; the chosen neighbourhoods cover the space. -/
theorem isFinitePresentation_determinant_of_isFlat {Y : RingedSpace.{u, u}}
    (G : SheafOfModules.{u} (structureSheafRing Y)) [G.IsFinitePresentation]
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier) G)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) G) :
    A.determinant.IsFinitePresentation := by
  let : ∀ V : Opens (Y.carrier : Type u),
      HasSheafify ((Opens.grothendieckTopology (Y.carrier : Type u)).over V) AddCommGrpCat.{u} :=
    fun _ => hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  let : ∀ V : Opens (Y.carrier : Type u),
      ((Opens.grothendieckTopology (Y.carrier : Type u)).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
    fun _ => GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  choose U hU p hp using fun x : Y.carrier =>
    exists_isFinite_presentation_determinant_over_of_isFlat G A hflat x
  have hcov : IsOpenCover U :=
    IsOpenCover.mk (le_antisymm le_top fun x _ => Opens.mem_iSup.mpr ⟨x, hU x⟩)
  exact Stacks.SheafOfModules.isFinitePresentation_of_coversTop U
    ((Opens.coversTop_iff _ U).mpr hcov) fun x => ⟨p x, hp x⟩

/-- **[Stacks, Tag 0FJN].** The determinant of a flat sheaf of modules of finite presentation on
a ringed space is an invertible module.

Its hypotheses on `F` are exactly the source's: `F` is flat, in the sense
`AlgebraicGeometry.SheafOfModules.IsFlat` that the source assumes, and of finite presentation.
Nothing is assumed about `det(F)`. Three statements stand behind it, each proved in this
repository: every stalk of `det(F)` is an invertible module
(`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant_stalk_invertible`, with Tag 05NE
turning flatness of the sheaf into flatness of the stalks); `det(F)` is of finite presentation
(`isFinitePresentation_determinant_of_isFlat` above); and invertibility descends from the stalks
for a sheaf of modules of finite presentation
(`Stacks.SheafOfModules.stalkwiseInvertibleDescent`).

**This is the whole covering set of Tag 0FJN.** The two other statements of the tag's
conclusion — `determinant_isInvertible` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorAlgebraDeterminant.lean` and
`determinant_isInvertible_of_finitePresentationDescent` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorAnnihilatorStalk.lean` — assume more than
this one and do not carry the attribute.

The statement lives here rather than beside
`determinant_stalk_invertible_of_isFlat`, which is where it was while the finite presentation of
`det(F)` was a hypothesis, because
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantInvertible` cannot import the
file that proves that finite presentation: the closure of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact`, which this file needs
through the two retract conditions, makes `HasCoproduct` unsynthesizable in the coproduct
section of that file, where a family of sheaves of modules on a space is summed. That is a
pre-existing incompatibility between those two files and has nothing to do with the determinant;
it is recorded here because it is the reason for the split. -/
@[stacks 0FJN "flatness and finite presentation of F are its only hypotheses on F, which is \
what the source assumes, and it carries no hypothesis about det(F)", sga "3 XV 5.7" "partial"]
theorem determinant_isInvertible_of_isFlat {Y : RingedSpace.{u, u}}
    (G : SheafOfModules.{u} (structureSheafRing Y)) [G.IsFinitePresentation]
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier) G)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) G) :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ Y.presheaf
        (forget₂ CommRingCat.{u} RingCat.{u}) Y.IsSheaf) A.determinant :=
  Stacks.SheafOfModules.stalkwiseInvertibleDescent Y A.determinant
    (isFinitePresentation_determinant_of_isFlat G A hflat)
    (determinant_stalk_invertible G A
      ((AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat Y.sheaf G).mp hflat))

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
