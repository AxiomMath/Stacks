module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSectionsOfColimit

/-!
# Sections over an affine chart of a filtered colimit of modules: the injective half

Let `M` be the colimit of a filtered diagram `D` of modules on the small étale site of an
algebraic space.  A section of a member `D k` over an étale chart with *affine* underlying scheme
which maps to zero in `M` already maps to zero in some later member `D l`.  Together with the
surjective half `AlgebraicGeometry.Space.exists_eq_of_isColimit_of_isQuasicoherentOnSite` this
says that, for quasi-coherent modules, the sections over an affine chart of a filtered colimit
are the colimit of the sections.

No quasi-coherence is needed for the injective half.  A colimit of sheaves is the
sheafification of the colimit of the underlying presheaves, and sheafification is locally
injective, so a section that dies in `M` dies locally in the presheaf colimit, that is, locally
at a later index.  An affine chart is quasi-compact, so finitely many local pieces suffice and a
filtered diagram absorbs the finitely many indices; the kernels of the transition maps out of
`D k` form a directed family of submodules, and
`AlgebraicGeometry.Space.exists_mem_of_directed_of_locally` does the bookkeeping.

## Main results

* `AlgebraicGeometry.Space.exists_map_eq_zero_of_isColimit`: the injective half.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- A section of a member of a filtered colimit of modules which dies in the colimit dies
locally at a later index. -/
private theorem exists_sieve_map_eq_zero_of_isColimit {K : Type u} [SmallCategory K]
    [IsFiltered K] {D : K ⥤ Modules.{u, u} B S hS F hF} {c : Cocone D} (hc : IsColimit c)
    {U : SmallEtale B S hS F} (k : K) (y : (D.obj k).val.obj (op U))
    (hy : (c.ι.app k).val.app (op U) y = 0) :
    ∃ R : Sieve U, R ∈ SmallEtale.topology B S hS F U ∧
      ∀ ⦃V : SmallEtale B S hS F⦄ (g : V ⟶ U), R g →
        ∃ (l : K) (f : k ⟶ l), (D.map f).val.app (op V) ((D.obj k).val.map g.op y) = 0 := by
  let J := SmallEtale.topology B S hS F
  let T := SheafOfModules.toSheaf.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  have : PreservesColimitsOfShape K T := SheafOfModules.preservesColimitsOfShape_toSheaf _
  have hc' : IsColimit (T.mapCocone c) := isColimitOfPreserves T hc
  let G : K ⥤ (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u} := (D ⋙ T) ⋙ sheafToPresheaf J _
  let P := colimit G
  let E := Sheaf.sheafifyCocone (colimit.cocone G)
  have hE : IsColimit E := Sheaf.isColimitSheafifyCocone _ (colimit.isColimit G)
  have h2 : (E.ι.app k).hom = colimit.ι G k ≫ toSheafify J P :=
    Sheaf.sheafifyCocone_ι_app_val _ k
  let a : P.obj (op U) := (colimit.ι G k).app (op U) y
  have ha : (toSheafify J P).app (op U) a = (toSheafify J P).app (op U) 0 := by
    rw [map_zero]
    have h3 : (E.ι.app k).hom.app (op U) y =
        (hc'.coconePointUniqueUpToIso hE).hom.hom.app (op U)
          ((c.ι.app k).val.app (op U) y) := by
      rw [← hc'.comp_coconePointUniqueUpToIso_hom hE k]
      rfl
    rw [hy] at h3
    have h4 : (E.ι.app k).hom.app (op U) y = (toSheafify J P).app (op U) a := by
      rw [h2]
      rfl
    exact h4.symm.trans (h3.trans (map_zero _))
  have hinj : Presheaf.IsLocallyInjective J (toSheafify J P) :=
    ((J.W_iff_isLocallyBijective _).1 (J.W_toSheafify P)).1
  refine ⟨Presheaf.equalizerSieve a 0, Presheaf.equalizerSieve_mem J (toSheafify J P) a 0 ha,
    fun V g hg => ?_⟩
  have hg' : P.map g.op a = P.map g.op 0 := hg
  have key : (colimit.ι G k).app (op V) ((D.obj k).val.map g.op y) =
      (colimit.ι G k).app (op V) 0 := by
    rw [map_zero] at hg' ⊢
    exact (NatTrans.naturality_apply (colimit.ι G k) g.op y).trans hg'
  have hV : IsColimit ((forget AddCommGrpCat.{u}).mapCocone
      (((evaluation _ _).obj (op V)).mapCocone (colimit.cocone G))) :=
    isColimitOfPreserves _ (isColimitOfPreserves _ (colimit.isColimit G))
  obtain ⟨l, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hV _ _).1 key
  refine ⟨l, f, ?_⟩
  have hf' : (G.map f).app (op V) ((D.obj k).val.map g.op y) = (G.map f).app (op V) 0 := hf
  rwa [map_zero] at hf'

/-- **Sections over an affine chart of a filtered colimit of modules: the injective half.**  If
`M` is the colimit of a filtered diagram `D` of modules on the small étale site of an algebraic
space, a section of `D k` over an étale chart with affine underlying scheme which maps to zero in
`M` already maps to zero in `D l` for some `k ⟶ l`.

No quasi-coherence is assumed.  With the surjective half
`AlgebraicGeometry.Space.exists_eq_of_isColimit_of_isQuasicoherentOnSite` it gives
`Γ(U, colim M_i) = colim Γ(U, M_i)` for an affine chart `U` and a filtered system of
quasi-coherent modules. -/
theorem exists_map_eq_zero_of_isColimit {K : Type u} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Modules.{u, u} B S hS F hF} {c : Cocone D} (hc : IsColimit c)
    {U : SmallEtale B S hS F}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)))
    (k : K) (y : (D.obj k).val.obj (op U)) (hy : (c.ι.app k).val.app (op U) y = 0) :
    ∃ (l : K) (f : k ⟶ l), (D.map f).val.app (op U) y = 0 := by
  let N : (Σ l : K, k ⟶ l) → (D.obj k).Submodule := fun p =>
    SheafOfModules.Submodule.ker (D.map p.2)
  have hle : ∀ (p : Σ l : K, k ⟶ l) {m : K} (h : p.1 ⟶ m), N p ≤ N ⟨m, p.2 ≫ h⟩ := by
    intro p m h X x hx
    change (D.map (p.2 ≫ h)).val.app X x = 0
    change (D.map p.2).val.app X x = 0 at hx
    rw [D.map_comp, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ConcreteCategory.comp_apply, hx, map_zero]
  have hdir : Directed (· ≤ ·) N := by
    intro p q
    let e := IsFiltered.coeq (p.2 ≫ IsFiltered.leftToMax p.1 q.1)
      (q.2 ≫ IsFiltered.rightToMax p.1 q.1)
    let h := IsFiltered.coeqHom (p.2 ≫ IsFiltered.leftToMax p.1 q.1)
      (q.2 ≫ IsFiltered.rightToMax p.1 q.1)
    have hw : (p.2 ≫ IsFiltered.leftToMax p.1 q.1) ≫ h =
        (q.2 ≫ IsFiltered.rightToMax p.1 q.1) ≫ h := IsFiltered.coeq_condition _ _
    refine ⟨⟨e, (p.2 ≫ IsFiltered.leftToMax p.1 q.1) ≫ h⟩, ?_, ?_⟩
    · simpa only [Category.assoc] using hle p (IsFiltered.leftToMax p.1 q.1 ≫ h)
    · rw [hw]
      simpa only [Category.assoc] using hle q (IsFiltered.rightToMax p.1 q.1 ≫ h)
  have : Nonempty (Σ l : K, k ⟶ l) := ⟨⟨k, 𝟙 k⟩⟩
  obtain ⟨R, hR, hloc⟩ := exists_sieve_map_eq_zero_of_isColimit hc k y hy
  obtain ⟨p, hp⟩ := exists_mem_of_directed_of_locally N hdir hU y hR
    (fun V g hg => by
      obtain ⟨l, f, hf⟩ := hloc g hg
      exact ⟨⟨l, f⟩, hf⟩)
  exact ⟨p.1, p.2, hp⟩

end AlgebraicGeometry.Space

end
