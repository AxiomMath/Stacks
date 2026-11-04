module

public import StacksFrontier.Deformation.ToposThickening.Helpers.RelativeBasePullbackIdealIncl
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickeningsIdealMap
public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.Helpers.IsoConjugateMap

/-!
# Maps of ideals of relative squares read through `f̃'^*𝒥̃ ≅ f'^*𝒥`

Let `iₖ : Y ⟶ Xₖ` (`k = 1, 2`) be first order thickenings sitting in the relative squares of
first order thickenings `tₖ : Sₖ ⟶ S'ₖ` along `f'ₖ : Xₖ ⟶ S'ₖ`, so that the induced maps of
ideals `ψₖ : f̃'ₖ^*𝒥̃ₖ ⟶ Iₖ` of
`Deformation.ToposThickening.MorphismOfThickenings.ofFirstOrderThickenings` are defined. A map
`ν' : f'₁^*𝒥₁ ⟶ J(f'₂^*𝒥₂)`, for a functor `J`, read through the identifications
`Deformation.ToposThickening.relBasePullbackIdealIso` of `f̃'ₖ^*𝒥̃ₖ` with `f'ₖ^*𝒥ₖ`, is
compatible with `ψ₁`, `J ψ₂` and a map `s` of the structure sheaves as soon as `ν'` is compatible
with the maps `f'ₖ^*𝒥ₖ ⟶ f'ₖ^*O ⟶ O_{Xₖ}` and `s`
(`Deformation.ToposThickening.relBasePullbackIdealIso_conj_comp_map_idealMap_comp_incl`).

This is the reduction of the ideal-square compatibility of the relative squares of `Coh_{X/B}`
(second proof of Stacks 08WA) to a statement on the bases. It is stated with all the sheaf
conditions of the sites as implicit arguments, so that it applies by unification to terms whose
instance arguments were found in other contexts.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u w v' u' vS uS vS' uS'

namespace CategoryTheory

/-- A map `eqToHom ≫ b₁ ≫ eqToHom ≫ ν' ≫ J(eqToHom ≫ b₂⁻¹ ≫ eqToHom)` is compatible with maps
`ψ₁ ≫ ι₁` and `J(ψ₂ ≫ ι₂)` and a map `s`, when `ν'` is compatible with maps `Aₖ ≫ Bₖ` and `s`,
and `eqToHom ≫ bₖ ≫ eqToHom ≫ Aₖ ≫ Bₖ = ψₖ ≫ ιₖ`. The identifications of objects in the
hypotheses are independent of those in the conclusion, so that each can be the one of its
source. -/
theorem eqToHom_comp_comp_eqToHom_comp_map_comp_map_eq_of_eq {C D : Type*} [Category* C]
    [Category* D] (J : C ⥤ D) {Q₁ M₁ U : D} {Q₂ M₂ U₂ : C} {ν' : Q₁ ⟶ J.obj Q₂}
    {A₁ : Q₁ ⟶ M₁} {B₁ : M₁ ⟶ U} {s s' : U ⟶ J.obj U₂} {A₂ : Q₂ ⟶ M₂} {B₂ : M₂ ⟶ U₂}
    (hH : ν' ≫ J.map (A₂ ≫ B₂) = A₁ ≫ B₁ ≫ s)
    {P₁ R₁ R₁' I₁ : D} (e₁ : P₁ = R₁) (b₁ : R₁ ≅ R₁') (e₁' : R₁' = Q₁) {z₁ : P₁ ⟶ U}
    (d₁ : P₁ = R₁) (d₁' : R₁' = Q₁)
    (h₁ : eqToHom d₁ ≫ b₁.hom ≫ eqToHom d₁' ≫ A₁ ≫ B₁ = z₁)
    {P₂ R₂ R₂' I₂ : C} (e₂ : R₂ = P₂) (b₂ : R₂ ≅ R₂') (e₂' : Q₂ = R₂') {z₂ : P₂ ⟶ U₂}
    (d₂ : P₂ = R₂) (d₂' : R₂' = Q₂)
    (h₂ : eqToHom d₂ ≫ b₂.hom ≫ eqToHom d₂' ≫ A₂ ≫ B₂ = z₂)
    {ψ₁ : P₁ ⟶ I₁} {ι₁ : I₁ ⟶ U} (hz₁ : ψ₁ ≫ ι₁ = z₁)
    {ψ₂ : P₂ ⟶ I₂} {ι₂ : I₂ ⟶ U₂} (hz₂ : ψ₂ ≫ ι₂ = z₂) (hs : s' = s) :
    (eqToHom e₁ ≫ b₁.hom ≫ eqToHom e₁' ≫ ν' ≫
        J.map (eqToHom e₂' ≫ b₂.inv ≫ eqToHom e₂)) ≫ J.map (ψ₂ ≫ ι₂) =
      ψ₁ ≫ ι₁ ≫ s' := by
  subst h₁ h₂ hs
  have k : eqToHom e₂' ≫ b₂.inv ≫ eqToHom e₂ ≫ eqToHom d₂ ≫ b₂.hom ≫ eqToHom d₂' ≫
      A₂ ≫ B₂ = A₂ ≫ B₂ := by
    simp
  rw [← Category.assoc ψ₁ ι₁ s', hz₁, hz₂]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [k, hH]

end CategoryTheory

namespace Deformation.ToposThickening

section IdealMap

variable {Y : RingedTopos.{v, u, w}} {X₁ : RingedTopos.{v', u', w}}
  {S₁ : RingedTopos.{vS, uS, w}} {S'₁ : RingedTopos.{vS', uS', w}}
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X₁.J.HasSheafCompose (forget RingCat.{w})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X₁.J.HasSheafCompose (forget CommRingCat.{w})]
  [HasWeakSheafify X₁.J AddCommGrpCat.{w}] [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X₁.J AddCommGrpCat.{w}]
  [S₁.J.HasSheafCompose (forget RingCat.{w})]
  [S₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S'₁.J.HasSheafCompose (forget RingCat.{w})]
  [S'₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S'₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]

omit [X₁.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The induced map of ideals of a relative square (Stacks 08M7), followed by the inclusion of the
upper ideal, is `f̃'^*` of the inclusion of `𝒥̃` followed by `f̃'^*O ⟶ O'`. -/
theorem ofFirstOrderThickenings_relBase_idealMap_comp_incl
    {t : RingedToposHom S₁ S'₁} {f' : RingedToposHom X₁ S'₁} (ht : FirstOrderThickening t)
    {i : RingedToposHom Y X₁} {f : RingedToposHom Y (relBaseBottom t f')}
    (hi : FirstOrderThickening i)
    (comm : (relBaseRight f').comp i = (relBaseThickening t f').comp f) :
    (MorphismOfThickenings.ofFirstOrderThickenings i (relBaseThickening t f') f
        (relBaseRight f') hi (relBaseThickeningFirstOrderThickening (f' := f') ht)
        comm).idealMap ≫ hi.idealOfThickening.incl =
      (pullbackModules (relBaseRight f').toModulesHom).map
          (relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.incl ≫
        RingedToposHom.pullbackUnitStructureMap (relBaseRight f') :=
  (MorphismOfThickenings.ofFirstOrderThickenings i (relBaseThickening t f') f
    (relBaseRight f') hi (relBaseThickeningFirstOrderThickening (f' := f') ht) comm).idealMap_spec


end IdealMap

section Transpose

variable {Y : RingedTopos.{v, u, w}} {X₁ X₂ : RingedTopos.{v', u', w}}
  {S₁ S₂ : RingedTopos.{vS, uS, w}} {S'₁ S'₂ : RingedTopos.{vS', uS', w}}
  {iY₁ : Y.J.HasSheafCompose (forget RingCat.{w})}
  {iY₂ : Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})}
  {iY₃ : Y.J.HasSheafCompose (forget AddCommGrpCat.{w})}
  {iX₁₁ : X₁.J.HasSheafCompose (forget RingCat.{w})}
  {iX₁₂ : X₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})}
  {iX₁₃ : X₁.J.HasSheafCompose (forget AddCommGrpCat.{w})}
  {iX₁₄ : X₁.J.HasSheafCompose (forget CommRingCat.{w})}
  {iX₁₅ : HasWeakSheafify X₁.J AddCommGrpCat.{w}}
  {iX₁₆ : X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}}
  {iX₁₇ : HasSheafify X₁.J AddCommGrpCat.{w}}
  {iX₂₁ : X₂.J.HasSheafCompose (forget RingCat.{w})}
  {iX₂₂ : X₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})}
  {iX₂₃ : X₂.J.HasSheafCompose (forget AddCommGrpCat.{w})}
  {iX₂₄ : X₂.J.HasSheafCompose (forget CommRingCat.{w})}
  {iX₂₅ : HasWeakSheafify X₂.J AddCommGrpCat.{w}}
  {iX₂₆ : X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}}
  {iX₂₇ : HasSheafify X₂.J AddCommGrpCat.{w}}
  {iS₁₁ : S₁.J.HasSheafCompose (forget RingCat.{w})}
  {iS₁₂ : S₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})}
  {iS₂₁ : S₂.J.HasSheafCompose (forget RingCat.{w})}
  {iS₂₂ : S₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})}
  {iS'₁₁ : S'₁.J.HasSheafCompose (forget RingCat.{w})}
  {iS'₁₂ : S'₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})}
  {iS'₁₃ : S'₁.J.HasSheafCompose (forget AddCommGrpCat.{w})}
  {iS'₂₁ : S'₂.J.HasSheafCompose (forget RingCat.{w})}
  {iS'₂₂ : S'₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})}
  {iS'₂₃ : S'₂.J.HasSheafCompose (forget AddCommGrpCat.{w})}

/-- **A map of the pulled-back ideals of the bases, read through `f̃'ₖ^*𝒥̃ₖ ≅ f'ₖ^*𝒥ₖ`, is
compatible with the induced maps of ideals of the relative squares.** If
`ν' : f'₁^*𝒥₁ ⟶ J(f'₂^*𝒥₂)` is compatible with the maps `f'ₖ^*𝒥ₖ ⟶ f'ₖ^*O ⟶ O_{Xₖ}` and `s`,
then `ν'` read through `Deformation.ToposThickening.relBasePullbackIdealIso` is compatible with
the induced maps `ψₖ : f̃'ₖ^*𝒥̃ₖ ⟶ Iₖ` of the relative squares (Stacks 08M7) followed by the
inclusions `Iₖ ⊂ O_{Xₖ}`, and `s`. -/
theorem relBasePullbackIdealIso_conj_comp_map_idealMap_comp_incl
    (J : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
    {t₁ : RingedToposHom S₁ S'₁} {f'₁ : RingedToposHom X₁ S'₁} {ht₁ : FirstOrderThickening t₁}
    {i₁ : RingedToposHom Y X₁} {f₁ : RingedToposHom Y (relBaseBottom t₁ f'₁)}
    {hi₁ : FirstOrderThickening i₁}
    {comm₁ : (relBaseRight f'₁).comp i₁ = (relBaseThickening t₁ f'₁).comp f₁}
    {t₂ : RingedToposHom S₂ S'₂} {f'₂ : RingedToposHom X₂ S'₂} {ht₂ : FirstOrderThickening t₂}
    {i₂ : RingedToposHom Y X₂} {f₂ : RingedToposHom Y (relBaseBottom t₂ f'₂)}
    {hi₂ : FirstOrderThickening i₂}
    {comm₂ : (relBaseRight f'₂).comp i₂ = (relBaseThickening t₂ f'₂).comp f₂}
    {e₁ : (pullbackModules (relBaseRight f'₁).toModulesHom).obj
        (relBaseThickeningFirstOrderThickening (f' := f'₁) ht₁).idealOfThickening.I =
      (pullbackModules (relBaseRight f'₁).toRingedToposModulesHom).obj
        (relBaseThickeningFirstOrderThickening (f' := f'₁) ht₁).idealOfThickening.I}
    {e₁' : (pullbackModules f'₁.toRingedToposModulesHom).obj ht₁.idealOfThickening.I =
      (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I}
    {e₂ : (pullbackModules (relBaseRight f'₂).toRingedToposModulesHom).obj
        (relBaseThickeningFirstOrderThickening (f' := f'₂) ht₂).idealOfThickening.I =
      (pullbackModules (relBaseRight f'₂).toModulesHom).obj
        (relBaseThickeningFirstOrderThickening (f' := f'₂) ht₂).idealOfThickening.I}
    {e₂' : (pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I =
      (pullbackModules f'₂.toRingedToposModulesHom).obj ht₂.idealOfThickening.I}
    {ν' : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      J.obj ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I)}
    {s s' : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O) ⟶
      J.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))}
    (hν' : ν' ≫ J.map ((pullbackModules f'₂.toModulesHom).map ht₂.idealOfThickening.incl ≫
        RingedToposHom.pullbackUnitStructureMap f'₂) =
      (pullbackModules f'₁.toModulesHom).map ht₁.idealOfThickening.incl ≫
        RingedToposHom.pullbackUnitStructureMap f'₁ ≫ s)
    (hs : s' = s) :
    (eqToHom e₁ ≫
        (relBasePullbackIdealIso t₁ f'₁ ht₁).hom ≫
        eqToHom e₁' ≫ ν' ≫
        J.map (eqToHom e₂' ≫
          (relBasePullbackIdealIso t₂ f'₂ ht₂).inv ≫
          eqToHom e₂)) ≫
      J.map ((MorphismOfThickenings.ofFirstOrderThickenings i₂ (relBaseThickening t₂ f'₂) f₂
          (relBaseRight f'₂) hi₂ (relBaseThickeningFirstOrderThickening (f' := f'₂) ht₂)
          comm₂).idealMap ≫ hi₂.idealOfThickening.incl) =
    (MorphismOfThickenings.ofFirstOrderThickenings i₁ (relBaseThickening t₁ f'₁) f₁
        (relBaseRight f'₁) hi₁ (relBaseThickeningFirstOrderThickening (f' := f'₁) ht₁)
        comm₁).idealMap ≫ hi₁.idealOfThickening.incl ≫ s' := by
  refine eqToHom_comp_comp_eqToHom_comp_map_comp_map_eq_of_eq J hν' e₁ _ e₁' _ _
    (relBasePullbackIdealIso_hom_comp_pullbackUnitStructureMap t₁ f'₁ ht₁) e₂ _ e₂' _ _
    (relBasePullbackIdealIso_hom_comp_pullbackUnitStructureMap t₂ f'₂ ht₂) ?_ ?_ hs
  · exact ofFirstOrderThickenings_relBase_idealMap_comp_incl ht₁ hi₁ comm₁
  · exact ofFirstOrderThickenings_relBase_idealMap_comp_incl ht₂ hi₂ comm₂


/-- The statement of `relBasePullbackIdealIso_conj_comp_map_idealMap_comp_incl` with every piece a
variable. The relative square is given by `τₖ`, `σₖ`, `hτₖ` equal to the thickening of the relative
base, the map `ν` is heterogeneously equal to
`eqToHom ≫ ρ₁ ≫ eqToHom ≫ ν' ≫ J'(eqToHom ≫ ρ₂⁻¹ ≫ eqToHom)` with `ρₖ` equal to
`Deformation.ToposThickening.relBasePullbackIdealIso`, and the compatibility of `ν'` with the maps
into the structure sheaves is given for maps equal to them. Every identification is a separate
hypothesis, so that each is checked on its own terms. -/
theorem relBasePullbackIdealIso_conj_comp_map_idealMap_comp_incl_of_heq
    (J : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
    {t₁ : RingedToposHom S₁ S'₁} {f'₁ : RingedToposHom X₁ S'₁} {ht₁ : FirstOrderThickening t₁}
    {i₁ : RingedToposHom Y X₁} {f₁ : RingedToposHom Y (relBaseBottom t₁ f'₁)}
    {hi₁ : FirstOrderThickening i₁}
    {τ₁ : RingedToposHom (relBaseBottom t₁ f'₁) (relBaseTop f'₁)}
    {σ₁ : RingedToposHom X₁ (relBaseTop f'₁)} {hτ₁ : FirstOrderThickening τ₁}
    {comm₁ : σ₁.comp i₁ = τ₁.comp f₁}
    {t₂ : RingedToposHom S₂ S'₂} {f'₂ : RingedToposHom X₂ S'₂} {ht₂ : FirstOrderThickening t₂}
    {i₂ : RingedToposHom Y X₂} {f₂ : RingedToposHom Y (relBaseBottom t₂ f'₂)}
    {hi₂ : FirstOrderThickening i₂}
    {τ₂ : RingedToposHom (relBaseBottom t₂ f'₂) (relBaseTop f'₂)}
    {σ₂ : RingedToposHom X₂ (relBaseTop f'₂)} {hτ₂ : FirstOrderThickening τ₂}
    {comm₂ : σ₂.comp i₂ = τ₂.comp f₂}
    {s' s : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O) ⟶
      J.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))}
    {ν : (pullbackModules σ₁.toModulesHom).obj hτ₁.idealOfThickening.I ⟶
      J.obj ((pullbackModules σ₂.toModulesHom).obj hτ₂.idealOfThickening.I)}
    {J' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)}
    {e₁ : (pullbackModules (relBaseRight f'₁).toModulesHom).obj
        (relBaseThickeningFirstOrderThickening (f' := f'₁) ht₁).idealOfThickening.I =
      (pullbackModules (relBaseRight f'₁).toRingedToposModulesHom).obj
        (relBaseThickeningFirstOrderThickening (f' := f'₁) ht₁).idealOfThickening.I}
    {ρ₁ : (pullbackModules (relBaseRight f'₁).toRingedToposModulesHom).obj
        (relBaseThickeningFirstOrderThickening (f' := f'₁) ht₁).idealOfThickening.I ≅
      (pullbackModules f'₁.toRingedToposModulesHom).obj ht₁.idealOfThickening.I}
    {e₁' : (pullbackModules f'₁.toRingedToposModulesHom).obj ht₁.idealOfThickening.I =
      (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I}
    {e₂ : (pullbackModules (relBaseRight f'₂).toRingedToposModulesHom).obj
        (relBaseThickeningFirstOrderThickening (f' := f'₂) ht₂).idealOfThickening.I =
      (pullbackModules (relBaseRight f'₂).toModulesHom).obj
        (relBaseThickeningFirstOrderThickening (f' := f'₂) ht₂).idealOfThickening.I}
    {ρ₂ : (pullbackModules (relBaseRight f'₂).toRingedToposModulesHom).obj
        (relBaseThickeningFirstOrderThickening (f' := f'₂) ht₂).idealOfThickening.I ≅
      (pullbackModules f'₂.toRingedToposModulesHom).obj ht₂.idealOfThickening.I}
    {e₂' : (pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I =
      (pullbackModules f'₂.toRingedToposModulesHom).obj ht₂.idealOfThickening.I}
    {ν' : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      J'.obj ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I)}
    {J'' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)}
    {ν'' : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      J''.obj ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I)}
    {A₁ : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      (pullbackModules f'₁.toModulesHom).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'₁.O))}
    {B₁ : (pullbackModules f'₁.toModulesHom).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'₁.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)}
    {A₂ : (pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I ⟶
      (pullbackModules f'₂.toModulesHom).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'₂.O))}
    {B₂ : (pullbackModules f'₂.toModulesHom).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'₂.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)}
    {s'' : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O) ⟶
      J''.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))}
    (eτ₁ : τ₁ = relBaseThickening t₁ f'₁) (eσ₁ : σ₁ = relBaseRight f'₁)
    (ehτ₁ : HEq hτ₁ (relBaseThickeningFirstOrderThickening (f' := f'₁) ht₁))
    (eτ₂ : τ₂ = relBaseThickening t₂ f'₂) (eσ₂ : σ₂ = relBaseRight f'₂)
    (ehτ₂ : HEq hτ₂ (relBaseThickeningFirstOrderThickening (f' := f'₂) ht₂))
    (hν : HEq ν (eqToHom e₁ ≫ ρ₁.hom ≫ eqToHom e₁' ≫ ν' ≫
      J'.map (eqToHom e₂' ≫ ρ₂.inv ≫ eqToHom e₂)))
    (hρ₁ : ρ₁ = relBasePullbackIdealIso t₁ f'₁ ht₁) (hρ₂ : ρ₂ = relBasePullbackIdealIso t₂ f'₂ ht₂)
    (hJ : J' = J)
    (hν' : ν'' ≫ J''.map (A₂ ≫ B₂) = A₁ ≫ B₁ ≫ s'')
    (hJ'' : J'' = J') (hν'' : HEq ν'' ν')
    (hA₁ : A₁ = (pullbackModules f'₁.toModulesHom).map ht₁.idealOfThickening.incl)
    (hB₁ : B₁ = RingedToposHom.pullbackUnitStructureMap f'₁)
    (hA₂ : A₂ = (pullbackModules f'₂.toModulesHom).map ht₂.idealOfThickening.incl)
    (hB₂ : B₂ = RingedToposHom.pullbackUnitStructureMap f'₂)
    (hs : s' = s) (hs'' : HEq s'' s) :
    ν ≫ J.map ((MorphismOfThickenings.ofFirstOrderThickenings i₂ τ₂ f₂ σ₂ hi₂ hτ₂
        comm₂).idealMap ≫ hi₂.idealOfThickening.incl) =
      (MorphismOfThickenings.ofFirstOrderThickenings i₁ τ₁ f₁ σ₁ hi₁ hτ₁ comm₁).idealMap ≫
        hi₁.idealOfThickening.incl ≫ s' := by
  subst eτ₁ eτ₂ eσ₁ eσ₂ ehτ₁ ehτ₂ hρ₁ hρ₂ hJ hJ'' hν'' hs'' hν hA₁ hA₂ hB₁ hB₂
  exact relBasePullbackIdealIso_conj_comp_map_idealMap_comp_incl _ hν' hs

/-- **The map of pulled-back ideals of a cube, read through `f̃'ₖ^*𝒥̃ₖ ≅ f'ₖ^*𝒥ₖ`, is `j^♯` on the
ideals of the relative squares.** Let `ν` be heterogeneously equal to
`CategoryTheory.isoConjugateMap` of `ν' : f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` through
`Deformation.ToposThickening.relBasePullbackIdealIso`, and let `ν'` be the transpose of a map
compatible with the maps `fₖ^*𝒥ₖ ⟶ fₖ^*O ⟶ O` and `j^♯` (the conclusion of
`CategoryTheory.Adjunction.homEquiv_symm_comp_map_comp_of_unit_maps` for the adjunctions
`f'ₖ^* ⊣ f'ₖ_*`). Then `ν` is compatible with the induced maps of ideals of the relative squares
(Stacks 08M7) and `j^♯`. Every piece is a variable identified with its value by a separate
hypothesis, so that each hypothesis is matched by the term that proves it. -/
theorem isoConjugateMap_comp_map_idealMap_comp_incl_of_heq
    {jj : RingedToposHom X₂ X₁}
    {t₁ : RingedToposHom S₁ S'₁} {f'₁ : RingedToposHom X₁ S'₁} {ht₁ : FirstOrderThickening t₁}
    {i₁ : RingedToposHom Y X₁} {f₁ : RingedToposHom Y (relBaseBottom t₁ f'₁)}
    {hi₁ : FirstOrderThickening i₁}
    {τ₁ : RingedToposHom (relBaseBottom t₁ f'₁) (relBaseTop f'₁)}
    {σ₁ : RingedToposHom X₁ (relBaseTop f'₁)} {hτ₁ : FirstOrderThickening τ₁}
    {comm₁ : σ₁.comp i₁ = τ₁.comp f₁}
    {t₂ : RingedToposHom S₂ S'₂} {f'₂ : RingedToposHom X₂ S'₂} {ht₂ : FirstOrderThickening t₂}
    {i₂ : RingedToposHom Y X₂} {f₂ : RingedToposHom Y (relBaseBottom t₂ f'₂)}
    {hi₂ : FirstOrderThickening i₂}
    {τ₂ : RingedToposHom (relBaseBottom t₂ f'₂) (relBaseTop f'₂)}
    {σ₂ : RingedToposHom X₂ (relBaseTop f'₂)} {hτ₂ : FirstOrderThickening τ₂}
    {comm₂ : σ₂.comp i₂ = τ₂.comp f₂}
    {s' : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O) ⟶
      jj.pushforwardModules.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))}
    {ν : (pullbackModules σ₁.toModulesHom).obj hτ₁.idealOfThickening.I ⟶
      jj.pushforwardModules.obj ((pullbackModules σ₂.toModulesHom).obj hτ₂.idealOfThickening.I)}
    {J' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)}
    {F₁ F'₁ G₁ G'₁ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)}
    {Z₁ : F₁ = F'₁} {ρ₁ : F'₁ ≅ G₁} {c₁ : G₁ = G'₁}
    {F₂ F'₂ G₂ G'₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)}
    {Z₂ : F₂ = F'₂} {ρ₂ : F'₂ ≅ G₂} {c₂ : G'₂ = G₂}
    {ν' : G'₁ ⟶ J'.obj G'₂}
    {J'' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)}
    {L₁ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S'₁.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)}
    {R₁ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S'₁.O)} {a₁ : L₁ ⊣ R₁}
    {L₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S'₂.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)}
    {R₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S'₂.O)} {a₂ : L₂ ⊣ R₂}
    {N₁ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S'₁.O)}
    {ι₁ : N₁ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'₁.O)}
    {s₁ : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'₁.O) ⟶
      R₁.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))}
    {N₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S'₂.O)}
    {ι₂ : N₂ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'₂.O)}
    {s₂ : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'₂.O) ⟶
      R₂.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))}
    {sj : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O) ⟶
      J''.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))}
    {ν'' : L₁.obj N₁ ⟶ J''.obj (L₂.obj N₂)}
    (eτ₁ : τ₁ = relBaseThickening t₁ f'₁) (eσ₁ : σ₁ = relBaseRight f'₁)
    (ehτ₁ : HEq hτ₁ (relBaseThickeningFirstOrderThickening (f' := f'₁) ht₁))
    (eτ₂ : τ₂ = relBaseThickening t₂ f'₂) (eσ₂ : σ₂ = relBaseRight f'₂)
    (ehτ₂ : HEq hτ₂ (relBaseThickeningFirstOrderThickening (f' := f'₂) ht₂))
    (hν : HEq ν (isoConjugateMap J' Z₁ ρ₁ c₁ ν' c₂ ρ₂ Z₂))
    (hF₁ : F₁ = (pullbackModules (relBaseRight f'₁).toModulesHom).obj
      (relBaseThickeningFirstOrderThickening (f' := f'₁) ht₁).idealOfThickening.I)
    (hF'₁ : F'₁ = (pullbackModules (relBaseRight f'₁).toRingedToposModulesHom).obj
      (relBaseThickeningFirstOrderThickening (f' := f'₁) ht₁).idealOfThickening.I)
    (hG₁ : G₁ = (pullbackModules f'₁.toRingedToposModulesHom).obj ht₁.idealOfThickening.I)
    (hG'₁ : G'₁ = (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I)
    (hF₂ : F₂ = (pullbackModules (relBaseRight f'₂).toModulesHom).obj
      (relBaseThickeningFirstOrderThickening (f' := f'₂) ht₂).idealOfThickening.I)
    (hF'₂ : F'₂ = (pullbackModules (relBaseRight f'₂).toRingedToposModulesHom).obj
      (relBaseThickeningFirstOrderThickening (f' := f'₂) ht₂).idealOfThickening.I)
    (hG₂ : G₂ = (pullbackModules f'₂.toRingedToposModulesHom).obj ht₂.idealOfThickening.I)
    (hG'₂ : G'₂ = (pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I)
    (hρ₁ : HEq ρ₁ (relBasePullbackIdealIso t₁ f'₁ ht₁))
    (hρ₂ : HEq ρ₂ (relBasePullbackIdealIso t₂ f'₂ ht₂))
    (hJ' : J' = jj.pushforwardModules)
    (hcube : ν'' ≫ J''.map (L₂.map ι₂ ≫ (a₂.homEquiv _ _).symm s₂) =
      L₁.map ι₁ ≫ (a₁.homEquiv _ _).symm s₁ ≫ sj)
    (hJ'' : J'' = jj.pushforwardModules) (hν'' : HEq ν'' ν')
    (hL₁ : L₁ = pullbackModules f'₁.toModulesHom) (hR₁ : R₁ = f'₁.pushforwardModules)
    (ha₁ : HEq a₁ (RingedToposHom.pullbackAdjPushforwardModules f'₁))
    (hN₁ : N₁ = ht₁.idealOfThickening.I) (hι₁ : HEq ι₁ ht₁.idealOfThickening.incl)
    (hs₁ : HEq s₁ (RingedToposHom.unitStructureMap f'₁))
    (hL₂ : L₂ = pullbackModules f'₂.toModulesHom) (hR₂ : R₂ = f'₂.pushforwardModules)
    (ha₂ : HEq a₂ (RingedToposHom.pullbackAdjPushforwardModules f'₂))
    (hN₂ : N₂ = ht₂.idealOfThickening.I) (hι₂ : HEq ι₂ ht₂.idealOfThickening.incl)
    (hs₂ : HEq s₂ (RingedToposHom.unitStructureMap f'₂))
    (hsj : HEq sj (RingedToposHom.unitStructureMap jj))
    (hs' : s' = RingedToposHom.unitStructureMap jj) :
    ν ≫ jj.pushforwardModules.map ((MorphismOfThickenings.ofFirstOrderThickenings i₂ τ₂ f₂ σ₂ hi₂
        hτ₂ comm₂).idealMap ≫ hi₂.idealOfThickening.incl) =
      (MorphismOfThickenings.ofFirstOrderThickenings i₁ τ₁ f₁ σ₁ hi₁ hτ₁ comm₁).idealMap ≫
        hi₁.idealOfThickening.incl ≫ s' := by
  subst eτ₁ eτ₂ eσ₁ eσ₂ hF₁ hF'₁ hG₁ hG'₁ hF₂ hF'₂ hG₂ hG'₂ hJ' hJ'' hL₁ hR₁ hL₂ hR₂ hN₁ hN₂ hs'
  subst ehτ₁ ehτ₂ hρ₁ hρ₂ ha₁ ha₂ hι₁ hι₂ hs₁ hs₂ hsj hν'' hν
  exact relBasePullbackIdealIso_conj_comp_map_idealMap_comp_incl _ hcube rfl

end Transpose

end Deformation.ToposThickening

end
