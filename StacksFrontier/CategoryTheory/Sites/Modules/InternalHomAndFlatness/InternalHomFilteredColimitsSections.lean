module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFilteredColimits
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetGlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# Hom out of a finitely presented module and filtered colimits

Let `(C, O)` be a ringed site, let `F` be an `O`-module of finite presentation and let
`G = colim_λ G_λ` be a filtered colimit of `O`-modules. Stacks 0GN0 asserts that

`colim_λ Hom_O(F, G_λ) = Hom_O(F, G)`,

*provided the hypotheses of Stacks 0GMR part (4) hold for the site `C`* (Stacks 0GMS discusses
when they do). That proviso is part of the source statement and is carried here as an explicit
hypothesis: without it the conclusion is false in general, since already for `F = O` it is the
assertion that global sections commute with the filtered colimit.

The proof is the one of the source. Write `H = Hom_O(F, colim G_λ)` and `H_λ = Hom_O(F, G_λ)`
for the *internal* Hom sheaves of Stacks 03EM. Then `Hom_O(F, -) = Γ(C, Hom_O(F, -))` as
functors, by Stacks 03EO applied to the unit module; `H = colim H_λ` by Stacks 0GMZ; and
`Γ(C, -)` commutes with filtered colimits by Stacks 0GMR (4). Composing the last two gives the
claim.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.sectionsFunctorIsoCoyonedaUnit`: the sections of a sheaf of
  modules are the morphisms out of the unit module, as a natural isomorphism of functors.
* `Stacks.SheafOfModules.InternalHom.coyonedaTensorUnitIsoInternalHomCoyoneda`: the
  hom-equivalence of Stacks 03EO at the monoidal unit, as a natural isomorphism in the target.
* `Stacks.SheafOfModules.InternalHom.coyonedaIsoInternalHomSections`: **`Hom_O(F, -)` is the
  global sections of the internal Hom sheaf `Hom_O(F, -)`**, as a natural isomorphism. This is
  the "by construction" step of the source, and it is where Stacks 03EO enters.

## Main results

* `Stacks.SheafOfModules.InternalHom.toSheaf_preservesColimitsOfShape` and
  `sheafCompose_forget_preservesColimitsOfShape`: the two functors through which a sheaf of
  modules becomes a sheaf of sets commute with the colimits at issue.
* `Stacks.SheafOfModules.InternalHom.sectionsFunctor_preservesColimitsOfShape`: under the
  hypothesis of Stacks 0GMR (4), global sections of sheaves of *modules* commute with filtered
  colimits. The library's form of Stacks 0GMR (4) is about sheaves of *sets*, so the passage goes
  through the two functors above.
* `Stacks.SheafOfModules.InternalHom.coyoneda_preservesColimitsOfShape_of_isFinitePresentation`:
  **Stacks 0GN0.**
* `Stacks.SheafOfModules.InternalHom.isIso_colimitPost_coyoneda_of_isFinitePresentation`: the
  same statement read as the source displays it, namely that the canonical comparison
  `colim_λ Hom_O(F, G_λ) ⟶ Hom_O(F, colim_λ G_λ)` is a bijection.
* `Stacks.SheafOfModules.InternalHom.coyoneda_preservesColimitsOfShape_of_coveringSet`:
  Stacks 0GN0 with the site hypothesis discharged by a covering set of quasi-compact sheaves as
  in Stacks 0GN3, which is one of the ways Stacks 0GMS offers to check the proviso.

## Implementation notes

Everything is equi-universe, as in
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFilteredColimits`:
the site has objects and morphisms in `Type u` and the structure sheaf is
`CommRingCat.{u}`-valued. This is the setting of Stacks 0GMZ, the key input, and of the
ringed-site development generally; it is also what makes the sheafification hypotheses free,
since such a site is essentially small in the module universe. It has the pleasant side effect
that the index category of the colimit may be taken in `Type u` with morphisms in `Type u`, so
that `Type u` and `AddCommGrpCat.{u}` have the relevant colimits outright and no universe
shrinking is needed anywhere.

The sheaf of rings in play is `Stacks.SheafOfModules.Tensor.ringSheaf X.O` throughout. The three
spellings this paragraph used to distinguish — among them the deleted
`AlgebraicGeometry.RingedSite.ringSheaf X` — have been merged onto that one declaration, so the
statements below, which spell it as Stacks 0GMZ does, and the monoidal machinery of Stacks 03EO
are taken over the same term.

The identification `Hom_O(F, G) = Γ(C, Hom_O(F, G))` is obtained from the adjunction of Stacks
03EO, read at the monoidal unit: `Hom(F ⊗ O, G) = Hom(O, Hom_O(F, G))`, the left-hand side is
`Hom(F, G)` by the right unitor and the right-hand side is the global sections of the internal
Hom sheaf. Taking it from the adjunction rather than from the object-level correspondence makes
the naturality in `G`, which is what the colimit comparison needs, come for free.

## References

* [Stacks Project, Tag 0GN0](https://stacks.math.columbia.edu/tag/0GN0)
* [Stacks Project, Tag 0GMZ](https://stacks.math.columbia.edu/tag/0GMZ)
* [Stacks Project, Tag 0GMR](https://stacks.math.columbia.edu/tag/0GMR)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

noncomputable section

namespace Stacks.SheafOfModules.InternalHom

universe u

section Sections

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor

/-- **Sections are morphisms out of the unit module, naturally.** The bijection
`SheafOfModules.unitHomEquiv` between the sections of a sheaf of modules and the morphisms from
the unit module into it, upgraded to a natural isomorphism of functors to types. -/
def sectionsFunctorIsoCoyonedaUnit :
    _root_.SheafOfModules.sectionsFunctor.{u} (Tensor.ringSheaf O) ≅
      coyoneda.obj (Opposite.op (_root_.SheafOfModules.unit (Tensor.ringSheaf O))) :=
  NatIso.ofComponents (fun M => (_root_.SheafOfModules.unitHomEquiv M).symm.toIso) (fun f => by
    ext s
    exact (_root_.SheafOfModules.unitHomEquiv_symm_comp s f).symm)

variable (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf O))

/-- **The adjunction of Stacks 03EO at the monoidal unit.** Morphisms out of `F ⊗ O` are
morphisms into the internal Hom sheaf out of `F`, naturally in the target; this is the
hom-equivalence of `reseatedTensorLeftAdjunction` read as a natural isomorphism of functors to
types, which is the form the colimit comparison needs. -/
def coyonedaTensorUnitIsoInternalHomCoyoneda :
    coyoneda.obj (Opposite.op ((tensorLeft F).obj (𝟙_ _))) ≅
      internalHomSecondFunctor.{u, u, u, u} J O F ⋙
        coyoneda.obj (Opposite.op
          (𝟙_ (_root_.SheafOfModules.{u} (Tensor.ringSheaf O)))) :=
  NatIso.ofComponents
    (fun G => ((reseatedTensorLeftAdjunction O F).homEquiv _ G).toIso)
    (fun g => by
      ext φ
      exact (reseatedTensorLeftAdjunction O F).homEquiv_naturality_right φ g)

/-- **`Hom_O(F, -)` is the global sections of the internal Hom sheaf `Hom_O(F, -)`.** This is
the step the source performs "by construction": the adjunction of Stacks 03EO read at the
monoidal unit `O` identifies `Hom(F, G) = Hom(F ⊗ O, G)` with `Hom(O, Hom_O(F, G))`, which is
the module of global sections of the internal Hom sheaf. -/
@[sga "3 III 0.6" "more general"]
def coyonedaIsoInternalHomSections :
    coyoneda.obj (Opposite.op F) ≅
      internalHomSecondFunctor.{u, u, u, u} J O F ⋙
        _root_.SheafOfModules.sectionsFunctor.{u} (Tensor.ringSheaf O) :=
  coyoneda.mapIso (ρ_ F).op ≪≫ coyonedaTensorUnitIsoInternalHomCoyoneda O F ≪≫
    Functor.isoWhiskerLeft _
      (eqToIso (congrArg (fun Z => coyoneda.obj (Opposite.op Z))
          (_root_.SheafOfModules.tensorUnit_sheafTensor O)) ≪≫
        (sectionsFunctorIsoCoyonedaUnit O).symm)

end Sections

section RingedSite

variable (X : RingedSite.{u, u, u})

/-- A site whose objects and morphisms lie in the module universe is essentially small
there. -/
local instance essentiallySmallSite_sections : EssentiallySmall.{u} X.C :=
  essentiallySmallSelf.{u, u, u} X.C

/-- Abelian presheaves on a site essentially small in the module universe are sheafifiable. -/
local instance hasSheafifyAbelian_sections : HasSheafify X.J AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u, u, u, u + 1, u} X.J _

/-- On a site essentially small in the module universe the maps inverted by sheafification of
abelian presheaves are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveAbelian_sections :
    X.J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u} X.J

/-- Sheafification of modules is left adjoint to the forgetful functor to presheaves, and
`SheafOfModules.toSheaf` factors the latter's left adjoint through abelian sheaves; so
`toSheaf` commutes with every colimit that `AddCommGrpCat.{u}` has. -/
theorem toSheaf_preservesColimitsOfShape (K : Type u) [Category.{u} K] :
    PreservesColimitsOfShape K (_root_.SheafOfModules.toSheaf.{u} (Tensor.ringSheaf X.O)) := by
  rw [(PresheafOfModules.sheafificationAdjunction
    (𝟙 (Tensor.ringSheaf X.O).obj)).preservesColimitsOfShape_iff]
  exact preservesColimitsOfShape_of_natIso
    (PresheafOfModules.sheafificationCompToSheaf (𝟙 (Tensor.ringSheaf X.O).obj)).symm

/-- Forgetting the group structure of an abelian sheaf commutes with filtered colimits, because
it does so on presheaves and both sheafification adjunctions are compatible with it. -/
theorem sheafCompose_forget_preservesColimitsOfShape (K : Type u) [Category.{u} K]
    [IsFiltered K] :
    PreservesColimitsOfShape K (sheafCompose X.J (forget AddCommGrpCat.{u})) := by
  rw [(sheafificationAdjunction X.J AddCommGrpCat.{u}).preservesColimitsOfShape_iff]
  exact preservesColimitsOfShape_of_natIso
    (sheafComposeNatIso X.J (forget AddCommGrpCat.{u})
      (sheafificationAdjunction X.J AddCommGrpCat.{u})
      (sheafificationAdjunction X.J (Type u)))

/-- **Global sections of sheaves of modules commute with filtered colimits**, under the
hypothesis of Stacks 0GMR part (4) on the site: there is a set `S` of sheaves of sets such that
every sheaf surjecting onto the final sheaf receives a map from a member of `S` which itself
surjects onto the final sheaf, and `K ⨯ K` is quasi-compact for every `K ∈ S`.

Stacks 0GMR (4) is about sheaves of sets, so the module statement is obtained by factoring the
sections functor as `SheafOfModules.toSheaf`, then the forgetful functor from abelian sheaves to
sheaves of sets, then `Sheaf.Γ`; the first two commute with filtered colimits and the third does
so by Stacks 0GMR (4). -/
theorem sectionsFunctor_preservesColimitsOfShape (K : Type u) [Category.{u} K] [IsFiltered K]
    (hX : ∃ S : Set (Sheaf X.J (Type u)),
      (∀ H : Sheaf X.J (Type u), Sheaf.IsLocallySurjective (terminal.from H) →
          ∃ L ∈ S, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ S, Sheaf.IsQuasiCompact (L ⨯ L)) :
    PreservesColimitsOfShape K
      (_root_.SheafOfModules.sectionsFunctor.{u} (Tensor.ringSheaf X.O)) := by
  have hΓ : PreservesColimitsOfShape K (Sheaf.Γ X.J (Type u)) := by
    constructor
    intro D
    have : IsIso (colimit.post D (Sheaf.Γ X.J (Type u))) :=
      (isIso_iff_bijective _).mpr
        ((Sheaf.injective_and_bijective_colimit_post_globalSections X.J D).2.2.2 hX)
    exact preservesColimit_of_isIso_post _ _
  have _ := toSheaf_preservesColimitsOfShape X K
  have _ := sheafCompose_forget_preservesColimitsOfShape X K
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft
      (_root_.SheafOfModules.toSheaf.{u} (Tensor.ringSheaf X.O) ⋙
        sheafCompose X.J (forget AddCommGrpCat.{u}))
      (Sheaf.ΓNatIsoSectionsFunctor X.J))

/-- **Stacks 0GN0.** On a ringed site satisfying the hypothesis of Stacks 0GMR part (4), Hom out
of a module `F` of finite presentation commutes with filtered colimits:

`colim_λ Hom_O(F, G_λ) = Hom_O(F, colim_λ G_λ)`.

The site hypothesis is the one the source attaches to the statement; it is needed already for
`F = O`, where the assertion is that global sections commute with the colimit. Stacks 0GMS
records sufficient conditions for it, one of which is applied in
`coyoneda_preservesColimitsOfShape_of_coveringSet` below. -/
@[stacks 0GN0, sga "4 VI 5.8" "special case"]
theorem coyoneda_preservesColimitsOfShape_of_isFinitePresentation
    (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)) [F.IsFinitePresentation]
    (K : Type u) [Category.{u} K] [IsFiltered K]
    (hX : ∃ S : Set (Sheaf X.J (Type u)),
      (∀ H : Sheaf X.J (Type u), Sheaf.IsLocallySurjective (terminal.from H) →
          ∃ L ∈ S, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ S, Sheaf.IsQuasiCompact (L ⨯ L)) :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op F)) := by
  have _ := internalHomSecondFunctor_preservesFilteredColimits X F K
  have _ := sectionsFunctor_preservesColimitsOfShape X K hX
  exact preservesColimitsOfShape_of_natIso (coyonedaIsoInternalHomSections X.O F).symm

/-- **Stacks 0GN0 as the source displays it.** The canonical comparison map
`colim_λ Hom_O(F, G_λ) ⟶ Hom_O(F, colim_λ G_λ)` is an isomorphism of types, for `F` of finite
presentation and a filtered diagram, under the hypothesis of Stacks 0GMR part (4). -/
theorem isIso_colimitPost_coyoneda_of_isFinitePresentation
    (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)) [F.IsFinitePresentation]
    {K : Type u} [Category.{u} K] [IsFiltered K]
    (D : K ⥤ _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O))
    (hX : ∃ S : Set (Sheaf X.J (Type u)),
      (∀ H : Sheaf X.J (Type u), Sheaf.IsLocallySurjective (terminal.from H) →
          ∃ L ∈ S, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ S, Sheaf.IsQuasiCompact (L ⨯ L)) :
    IsIso (colimit.post D (coyoneda.obj (Opposite.op F))) :=
  have _ := coyoneda_preservesColimitsOfShape_of_isFinitePresentation X F K hX
  inferInstance

/-- **Stacks 0GN0 with the site hypothesis discharged by a covering set of quasi-compact
sheaves.** If the site carries a set `S` of sheaves of sets as in Stacks 0GN3 — a member of `S`
surjects onto the final sheaf, a surjection onto a member of `S` is lifted by a member of `S`,
the product of two members of `S` receives a surjection from a member of `S`, and every member
of `S` is quasi-compact — then Hom out of a module of finite presentation commutes with filtered
colimits. This is one of the ways Stacks 0GMS offers to check the proviso of the source. -/
theorem coyoneda_preservesColimitsOfShape_of_coveringSet
    (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)) [F.IsFinitePresentation]
    (K : Type u) [Category.{u} K] [IsFiltered K] {S : Set (Sheaf X.J (Type u))}
    (h_terminal : ∃ L ∈ S, Sheaf.IsLocallySurjective (terminal.from L))
    (h_lift : ∀ {H L : Sheaf X.J (Type u)} (f : H ⟶ L), L ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ L' ∈ S, ∃ g : L' ⟶ H, Sheaf.IsLocallySurjective (g ≫ f))
    (h_product : ∀ L ∈ S, ∀ L' ∈ S,
      ∃ L'' ∈ S, ∃ f : L'' ⟶ L ⨯ L', Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ L ∈ S, Sheaf.IsQuasiCompact L) :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op F)) :=
  coyoneda_preservesColimitsOfShape_of_isFinitePresentation X F K
    ⟨S, fun _ hH =>
        Sheaf.exists_mem_hom_isLocallySurjective_terminal_of_coveringSet h_terminal h_lift _ hH,
      fun _ hL => Sheaf.isQuasiCompact_prod_self_of_coveringSet h_product h_quasiCompact _ hL⟩

end RingedSite

end Stacks.SheafOfModules.InternalHom

end

end
