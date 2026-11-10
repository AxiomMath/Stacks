module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule

/-!
# The quotient `𝓕/𝓘𝓕` of a module by the ideal of a closed subspace

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `𝓘 = ker(i♯) ⊆ 𝒪_X` be the quasi-coherent ideal cutting out `Z`, and let `𝓕`
be an arbitrary `𝒪_X`-module.  [Stacks, Tag 04CJ], part (1) says that the unit
`η_𝓕 : 𝓕 ⟶ i_*i^*𝓕` of the adjunction of Stacks 03LU induces an isomorphism

`𝓕/𝓘𝓕 ≅ i_*i^*𝓕`.

This file proves it, unconditionally.

The product `𝓘𝓕` is `Stacks.Sites.idealSmul` of the ideal with all of `𝓕`: the smallest
submodule of `𝓕` with local membership whose sections over every étale chart contain every
product of a section of `𝓘` with a section of `𝓕`.  The quotient `𝓕/𝓘𝓕` is the cokernel of its
inclusion, and the isomorphism below is the one `CategoryTheory.Limits.cokernel.desc` produces
from `η_𝓕`, so the displayed equation `cokernel.π ≫ e.hom = η_𝓕` holds by construction: the
isomorphism *is* the one induced by the adjunction, which is what the source asserts and what
makes the statement more than an abstract comparison of two quotients.

## Main definitions

* `AlgebraicGeometry.Space.kerIdealSmul`: the submodule `𝓘𝓕 ⊆ 𝓕`.
* `AlgebraicGeometry.Space.kerIdealSmulQuotient`: the quotient `𝓕/𝓘𝓕`.
* `AlgebraicGeometry.Space.kerIdealSmulQuotientUnitMap`: the map `𝓕/𝓘𝓕 ⟶ i_*i^*𝓕` induced by the
  unit of the adjunction of Stacks 03LU.
* `AlgebraicGeometry.Space.kerIdealSmulQuotientUnitIso`: **Stacks 04CJ, part (1)** — that map is
  an isomorphism.

## Main results

* `AlgebraicGeometry.Space.idealSmul_kerIdeal_le_ker_modulePullbackAdjunction_unit`: `𝓘𝓕` is
  contained in the kernel of the unit, which is what lets the unit factor through the quotient.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_kerIdealSmulQuotient`: `𝓘` annihilates `𝓕/𝓘𝓕`.
* `AlgebraicGeometry.Space.isIso_kerIdealSmulQuotientUnitMap`: **Stacks 04CJ, part (1)**, in the
  form of invertibility of the induced map.

## The proof

Both halves use the unconditional essential-image clause
`AlgebraicGeometry.Space.essImage_modulePushforward_iff`: an `𝒪_X`-module is a direct image along
`i` exactly when `𝓘` annihilates it.

*Surjectivity.*  The unit is an epimorphism at every module, which is
`AlgebraicGeometry.Space.epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated` with its
hypothesis discharged by that clause.  The induced map is a right factor of the unit through the
epimorphism `cokernel.π`, hence an epimorphism itself.

*Injectivity.*  `𝓘` annihilates `𝓕/𝓘𝓕`: a section of the quotient over a chart is, over a
covering sieve, the image of a section `t` of `𝓕`, and there `a · t` is a section of `𝓘𝓕` and so
dies in the quotient; a sheaf is separated, so the product was already zero.  Hence the unit at
`𝓕/𝓘𝓕` is invertible, and naturality of the unit at `cokernel.π` writes it as the induced map
followed by `i_*i^*(cokernel.π)`.  A left factor of a monomorphism is a monomorphism.

A monomorphism which is an epimorphism in an abelian category is an isomorphism.

## Implementation notes

The ideal is `SheafOfModules.kerIdeal` of the structure map `i♯`, the same spelling as in
`AlgebraicGeometry.Space.AnnihilatedByKerIdeal`, so the annihilation statements below apply to it
with no comparison; `AlgebraicGeometry.Space.kernelIdealSheaf` and
`AlgebraicGeometry.Space.definingIdealSheaf` have the same sections.

The product is `Stacks.Sites.idealSmul 𝓘 ⊤` rather than a new definition; it is the `n = 1` case
of `AlgebraicGeometry.Space.idealPowSubmodule`, by
`AlgebraicGeometry.Space.idealPowSubmodule_one`.

The modules are those of `AlgebraicGeometry.Space.Modules`, whose sections live in the universe
`u` of the schemes; that is the universe at which
`AlgebraicGeometry.Space.modulePullbackAdjunction` and the abelian structure of the category are
available.

## References

* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- **The submodule `𝓘𝓕 ⊆ 𝓕`** cut out by the ideal `𝓘 = ker(i♯)` of a morphism `i : Z ⟶ X` of
algebraic spaces: the smallest submodule with local membership whose sections over an étale chart
contain every product of a section of `𝓘` with a section of `𝓕`.

This is `Stacks.Sites.idealSmul` at the kernel ideal of the structure map, equivalently the
`n = 1` case of `AlgebraicGeometry.Space.idealPowSubmodule`. -/
abbrev kerIdealSmul (i : Z ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2) : F.Submodule :=
  idealPowSubmodule (SheafOfModules.kerIdeal (structureSharp B S hS i)) 1 F

/-- `𝓘𝓕` is the product of the ideal with all of `𝓕`, in the spelling of
`Stacks.Sites.idealSmul`. -/
theorem kerIdealSmul_eq_idealSmul (i : Z ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2) :
    kerIdealSmul B S hS i F =
      Stacks.Sites.idealSmul (SheafOfModules.kerIdeal (structureSharp B S hS i))
        (⊤ : F.Submodule) :=
  idealPowSubmodule_one _ F

/-- A product of a section of the ideal `𝓘 = ker(i♯)` with a section of `𝓕` over the same étale
chart is a section of `𝓘𝓕` there. -/
theorem smul_mem_kerIdealSmul (i : Z ⟶ X) {F : Modules.{u, u} B S hS X.1 X.2}
    {U : (SmallEtale B S hS X.1)ᵒᵖ} {a : (structureRingSheaf B S hS X).obj.obj U}
    (ha : a ∈ (SheafOfModules.kerIdeal (structureSharp B S hS i)).obj U) (m : F.val.obj U) :
    letI : Module ((structureRingSheaf B S hS X).obj.obj U) (F.val.obj U) :=
      (F.val.obj U).isModule
    a • m ∈ (kerIdealSmul B S hS i F).obj U :=
  smul_mem_idealPowSubmodule _
    ((Stacks.Sites.idealPow_one (SheafOfModules.kerIdeal (structureSharp B S hS i))).ge U ha) m

/-- **`𝓘𝓕` is contained in the kernel of the unit `η_𝓕 : 𝓕 ⟶ i_*i^*𝓕`.**

The ideal annihilates every direct image
(`AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`), so the unit carries a
product `a · m` with `a` a section of `𝓘` to `a · η_𝓕(m) = 0`; the kernel of a morphism is a
submodule with local membership, and `𝓘𝓕` is the smallest one containing those products. -/
theorem idealSmul_kerIdeal_le_ker_modulePullbackAdjunction_unit (i : Z ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    kerIdealSmul B S hS i F ≤
      SheafOfModules.Submodule.ker ((modulePullbackAdjunction B S hS i).unit.app F) := by
  refine idealPowSubmodule_le _ 1 fun U a ha m => ?_
  have ha' : a ∈ (SheafOfModules.kerIdeal (structureSharp B S hS i)).obj U :=
    (Stacks.Sites.idealPow_one (SheafOfModules.kerIdeal (structureSharp B S hS i))).le U ha
  change ((modulePullbackAdjunction B S hS i).unit.app F).val.app U (a • m) = 0
  rw [map_smul]
  exact annihilatedByKerIdeal_modulePushforward B S hS i ((modulePullback B S hS i).obj F) U a ha'
    _

/-- **The quotient `𝓕/𝓘𝓕`** of an `𝒪_X`-module by the ideal cutting out a closed subspace: the
cokernel of the inclusion of `AlgebraicGeometry.Space.kerIdealSmul`. -/
abbrev kerIdealSmulQuotient (i : Z ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS X.1 X.2 :=
  cokernel (kerIdealSmul B S hS i F).ι

/-- **The map `𝓕/𝓘𝓕 ⟶ i_*i^*𝓕` induced by the unit** of the adjunction of Stacks 03LU.  It
exists because the unit kills `𝓘𝓕`. -/
def kerIdealSmulQuotientUnitMap (i : Z ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2) :
    kerIdealSmulQuotient B S hS i F ⟶
      (modulePushforward B S hS i).obj ((modulePullback B S hS i).obj F) :=
  cokernel.desc _ ((modulePullbackAdjunction B S hS i).unit.app F)
    ((submodule_ι_comp_eq_zero_iff B S hS X.1 X.2 (kerIdealSmul B S hS i F)
      ((modulePullbackAdjunction B S hS i).unit.app F)).2
      (idealSmul_kerIdeal_le_ker_modulePullbackAdjunction_unit B S hS i F))

/-- **The induced map is the one that comes from the adjunction**: composing the projection onto
the quotient with it gives back the unit. -/
@[reassoc (attr := simp)]
theorem cokernel_π_comp_kerIdealSmulQuotientUnitMap (i : Z ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    cokernel.π (kerIdealSmul B S hS i F).ι ≫ kerIdealSmulQuotientUnitMap B S hS i F =
      (modulePullbackAdjunction B S hS i).unit.app F :=
  cokernel.π_desc _ _ _

/-- **The ideal cutting out the closed subspace annihilates the quotient `𝓕/𝓘𝓕`.**

A section of the quotient over an étale chart is, after restriction along the arrows of a
covering sieve, the image of a section `t` of `𝓕`
(`Stacks.SheafOfModules.EpiMono.exists_covering_of_epi`, the projection being an epimorphism).
There the product with a section `a` of `𝓘` is the image of `a · t`, which is a section of `𝓘𝓕`
and therefore dies in the quotient
(`AlgebraicGeometry.Space.cokernel_π_app_eq_zero_iff`).  A sheaf is separated, so the product was
already zero over the chart itself. -/
theorem annihilatedByKerIdeal_kerIdealSmulQuotient (i : Z ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    AnnihilatedByKerIdeal B S hS i (kerIdealSmulQuotient B S hS i F) := by
  intro U a ha m
  obtain ⟨T, hT, hsec⟩ :=
    Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
      (cokernel.π (kerIdealSmul B S hS i F).ι) (V := U.unop) m
  refine Stacks.eq_of_isSeparated _ hT fun W g hg => ?_
  obtain ⟨t, ht⟩ := hsec g hg
  change ↑(F.val.obj (op W)) at t
  have hm : (kerIdealSmulQuotient B S hS i F).val.map g.op m =
      (cokernel.π (kerIdealSmul B S hS i F).ι).val.app (op W) t := ht.symm
  refine Eq.trans ?_
    (map_zero (ConcreteCategory.hom
      ((kerIdealSmulQuotient B S hS i F).val.map g.op))).symm
  refine (PresheafOfModules.map_smul (kerIdealSmulQuotient B S hS i F).val g.op a m).trans ?_
  rw [hm]
  refine (((cokernel.π (kerIdealSmul B S hS i F).ι).val.app (op W)).hom.map_smul
    ((structureRingSheaf B S hS X).obj.map g.op a) t).symm.trans ?_
  exact (cokernel_π_app_eq_zero_iff B S hS X.1 X.2 (kerIdealSmul B S hS i F) (op W) _).2
    (smul_mem_kerIdealSmul B S hS i
      ((SheafOfModules.kerIdeal (structureSharp B S hS i)).map_mem g.op ha) t)

/-- **Stacks 04CJ, part (1)**, as invertibility of the induced map: for a closed immersion
`i : Z ⟶ X` of algebraic spaces and any `𝒪_X`-module `𝓕`, the map `𝓕/𝓘𝓕 ⟶ i_*i^*𝓕` induced by
the unit of the adjunction of Stacks 03LU is an isomorphism.

It is an epimorphism because the unit is
(`AlgebraicGeometry.Space.epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated`, whose
hypothesis is `AlgebraicGeometry.Space.essImage_modulePushforward_iff`), and a
monomorphism because the unit at `𝓕/𝓘𝓕` is invertible — that quotient being annihilated by `𝓘`
— and naturality exhibits the induced map as a left factor of it. -/
theorem isIso_kerIdealSmulQuotientUnitMap (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    IsIso (kerIdealSmulQuotientUnitMap B S hS i F) := by
  have hunit : ∀ G : Modules.{u, u} B S hS X.1 X.2,
      Epi ((modulePullbackAdjunction B S hS i).unit.app G) :=
    epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS i hi
      fun M hM => essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi M hM
  have hepi : Epi (kerIdealSmulQuotientUnitMap B S hS i F) := by
    have h : Epi (cokernel.π (kerIdealSmul B S hS i F).ι ≫
        kerIdealSmulQuotientUnitMap B S hS i F) := by
      rw [cokernel_π_comp_kerIdealSmulQuotientUnitMap]
      exact hunit F
    exact epi_of_epi (cokernel.π (kerIdealSmul B S hS i F).ι) _
  have hQ : IsIso ((modulePullbackAdjunction B S hS i).unit.app
      (kerIdealSmulQuotient B S hS i F)) :=
    (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS i hi _).1
      ((essImage_modulePushforward_iff B S hS i hi _).2
        (annihilatedByKerIdeal_kerIdealSmulQuotient B S hS i F))
  have hfac : kerIdealSmulQuotientUnitMap B S hS i F ≫
      (modulePullback B S hS i ⋙ modulePushforward B S hS i).map
        (cokernel.π (kerIdealSmul B S hS i F).ι) =
      (modulePullbackAdjunction B S hS i).unit.app (kerIdealSmulQuotient B S hS i F) := by
    refine (cancel_epi (cokernel.π (kerIdealSmul B S hS i F).ι)).1 ?_
    rw [← Category.assoc, cokernel_π_comp_kerIdealSmulQuotientUnitMap]
    exact (modulePullbackAdjunction B S hS i).unit_naturality
      (cokernel.π (kerIdealSmul B S hS i F).ι)
  have hmono : Mono (kerIdealSmulQuotientUnitMap B S hS i F) :=
    have : Mono ((modulePullbackAdjunction B S hS i).unit.app
        (kerIdealSmulQuotient B S hS i F)) := IsIso.mono_of_iso _
    mono_of_mono_fac hfac
  exact isIso_of_mono_of_epi _

/-- **Stacks 04CJ, part (1).**  Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over
`S` and let `𝓘 = ker(i♯) ⊆ 𝒪_X` be the ideal cutting out `Z`.  For every `𝒪_X`-module `𝓕` the
unit `𝓕 ⟶ i_*i^*𝓕` of the adjunction of Stacks 03LU induces an isomorphism `𝓕/𝓘𝓕 ≅ i_*i^*𝓕`.

The isomorphism is the one the adjunction gives: `cokernel.π ≫ e.hom` is the unit, by
`AlgebraicGeometry.Space.cokernel_π_comp_kerIdealSmulQuotientUnitMap`. -/
@[stacks 04CJ "part (1): the unit identifies the quotient by the defining ideal with the direct \
image of the inverse image"]
def kerIdealSmulQuotientUnitIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    kerIdealSmulQuotient B S hS i F ≅
      (modulePushforward B S hS i).obj ((modulePullback B S hS i).obj F) :=
  have := isIso_kerIdealSmulQuotientUnitMap B S hS i hi F
  asIso (kerIdealSmulQuotientUnitMap B S hS i F)

/-- **Stacks 04CJ, part (1)**, the normalisation of the isomorphism: it is induced by the unit of
the adjunction of Stacks 03LU, that is, composing the projection `𝓕 ⟶ 𝓕/𝓘𝓕` with it gives the
unit. -/
@[stacks 04CJ "part (1): the isomorphism is the one induced by the unit of the adjunction"]
theorem cokernel_π_comp_kerIdealSmulQuotientUnitIso_hom (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    cokernel.π (kerIdealSmul B S hS i F).ι ≫
        (kerIdealSmulQuotientUnitIso B S hS i hi F).hom =
      (modulePullbackAdjunction B S hS i).unit.app F :=
  cokernel_π_comp_kerIdealSmulQuotientUnitMap B S hS i F

end AlgebraicGeometry.Space

end
