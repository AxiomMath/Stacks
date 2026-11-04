module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCode
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraAffineTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.LocallyConcentratedFormality

/-!
# Finitely presented quasi-coherent modules on an affine representable space

Let `U` be an object of a big fppf site whose underlying scheme is affine. A quasi-coherent
`𝒪`-module of finite presentation on the small étale site of `yoneda.obj U` has a finite global
presentation on the slice at the identity chart, which is terminal, and so it is determined up to
isomorphism by the code of that presentation
(`SheafOfModules.FinitePresentationData.code`), a finite matrix of global functions on `U`. In
particular these modules have at most `max ℵ₀ #Γ(U, ⊤)` isomorphism classes.

## Main results

* `AlgebraicGeometry.Space.nonempty_iso_of_over_isTerminal`: two modules on the small étale site
  of a presheaf whose restrictions to the slice at a terminal object are isomorphic are
  isomorphic.
* `AlgebraicGeometry.Space.exists_code_of_isTerminal`: the codes, as an injection of the
  isomorphism classes of finitely presented quasi-coherent modules into the finite matrices over
  the ring of sections over an affine terminal chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

/-- A finitely generated module over a ring `A` has at most `max ℵ₀ #A` elements. -/
theorem Cardinal.mk_le_of_module_finite (A M : Type u) [Ring A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] : #M ≤ max ℵ₀ #A := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have hsurj : Function.Surjective (fun c : Fin n → A => ∑ i, c i • s i) := fun x =>
    (Submodule.mem_span_range_iff_exists_fun A).1 (by simp [hs])
  calc #M ≤ #(Fin n → A) := mk_le_of_surjective hsurj
    _ ≤ max ℵ₀ #A := by
      rw [show #(Fin n → A) = #A ^ (n : Cardinal) by simp]
      exact (power_le_power_right (le_max_right _ _)).trans (power_nat_le (le_max_left _ _))

namespace SheafOfModules

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- On a site with a terminal object `X`, a global section of a sheaf of modules is determined by
its value at `X`. -/
theorem sections_eval_injective_of_isTerminal {X : C} (hX : IsTerminal X)
    (N : SheafOfModules.{u} R) :
    Function.Injective (fun s : N.sections => s.1 (op X)) := by
  intro s s' h
  apply Subtype.ext
  funext Y
  have key (t : N.sections) :
      (N.val.presheaf ⋙ CategoryTheory.forget _).map (hX.from Y.unop).op (t.1 (op X)) = t.1 Y :=
    t.2 _
  rw [← key s, ← key s']
  exact congrArg _ h

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Two modules whose restrictions to the slice at a terminal object are isomorphic are
isomorphic.** The slice at a terminal object is the site again, and restricting to it and back
returns the module on the nose. -/
theorem nonempty_iso_of_over_isTerminal {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (R : Sheaf (SmallEtale.topology B S hS F) RingCat.{u})
    {T : SmallEtale B S hS F} (hT : IsTerminal T) {M M' : SheafOfModules.{u} R}
    (e : M.over T ≅ M'.over T) : Nonempty (M ≅ M') := by
  let hds : (Over.forget T).IsDenseSubsite
      ((SmallEtale.topology B S hS F).over T) (SmallEtale.topology B S hS F) :=
    CategoryTheory.GrothendieckTopology.isDenseSubsite_overForget
      (SmallEtale.topology B S hS F) hT
  let _hds' : ((Over.equivalenceOfIsTerminal hT).symm).inverse.IsDenseSubsite
      ((SmallEtale.topology B S hS F).over T) (SmallEtale.topology B S hS F) := hds
  let _hds'' : ((Over.equivalenceOfIsTerminal hT).symm).functor.IsDenseSubsite
      (SmallEtale.topology B S hS F) ((SmallEtale.topology B S hS F).over T) := inferInstance
  let _hc : ((Over.equivalenceOfIsTerminal hT).symm).inverse.IsContinuous
      ((SmallEtale.topology B S hS F).over T) (SmallEtale.topology B S hS F) :=
    inferInstanceAs ((Over.forget T).IsContinuous
      ((SmallEtale.topology B S hS F).over T) (SmallEtale.topology B S hS F))
  let E : SmallEtale B S hS F ≌ Over T := (Over.equivalenceOfIsTerminal hT).symm
  let φ : R ⟶ Stacks.SheafOfModules.reindexRing (SmallEtale.topology B S hS F) E (R.over T) :=
    𝟙 (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B S hS F) E (R.over T))
  let F₀ := SheafOfModules.pushforward.{u} φ
  have key : ∀ N : SheafOfModules.{u} R, F₀.obj (N.over T) ≅ N := fun N =>
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))
  exact ⟨(key M).symm ≪≫ F₀.mapIso e ≪≫ key M'⟩


variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  {T : (smallEtaleRingedSite B S hS F hF).C}

/-- **A finitely presented quasi-coherent module has a finite global presentation on the slice at
an affine chart.** -/
theorem hasFiniteGlobalPresentation_over_of_isAffine
    (hTa : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj T))
    (G : Modules.{u, u} B S hS F hF)
    (hq : G.IsQuasicoherentOnSite) (hfp : SheafOfModules.IsFinitePresentationOnSite G) :
    SheafOfModules.HasFiniteGlobalPresentation (G.over T) :=
  hasFiniteGlobalPresentation_over_of_moduleFinitePresentation B S hS F hF G
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G hq) T hTa
    (module_finitePresentation_sections_of_isFinitePresentationOnSite G hq hfp T hTa)

/-- The endomorphisms of the lifted structure sheaf of a slice of the small étale site embed into
the ring of sections over the chart: they are the global sections, and a global section on the
slice is determined by its value at the identity. -/
theorem exists_injective_endUlift_over (T : (smallEtaleRingedSite B S hS F hF).C) :
    ∃ f : (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over
              T)) ⟶
        SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over
              T))) → chartRing B S hS F hF T,
      Function.Injective f := by
  let N := SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over T)
  let e := Stacks.SheafOfModules.uliftForPresentationSectionsEquiv N
  exact ⟨fun x => (e x).1 (op (Over.mk (𝟙 T))),
    (SheafOfModules.sections_eval_injective_of_isTerminal Over.mkIdTerminal N).comp e.injective⟩

/-- **The isomorphism classes of finitely presented quasi-coherent modules on the small étale
site of an algebraic space with an affine terminal chart `T` inject into the finite matrices over
the ring of sections over `T`.** -/
theorem exists_code_of_isTerminal (hT : IsTerminal T)
    (hTa : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj T)) :
    ∃ c : {G : Modules.{u, u} B S hS F hF //
        G.IsQuasicoherentOnSite ∧ SheafOfModules.IsFinitePresentationOnSite G} →
        (Σ n k : ℕ, Fin k → Fin n → chartRing B S hS F hF T),
      ∀ G G', c G = c G' → Nonempty (G.1 ≅ G'.1) := by
  classical
  obtain ⟨f, hf⟩ := exists_injective_endUlift_over hF T
  let d : ∀ G : {G : Modules.{u, u} B S hS F hF //
      G.IsQuasicoherentOnSite ∧ SheafOfModules.IsFinitePresentationOnSite G},
      SheafOfModules.FinitePresentationData (G.1.over T) := fun G =>
    (SheafOfModules.nonempty_finitePresentationData
      (hasFiniteGlobalPresentation_over_of_isAffine hF hTa G.1 G.2.1 G.2.2)).some
  let g : SheafOfModules.PresentationCode
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over T) →
      (Σ n k : ℕ, Fin k → Fin n → chartRing B S hS F hF T) :=
    fun x => ⟨x.1, x.2.1, fun j i => f (x.2.2 j i)⟩
  have hg : Function.Injective g := by
    rintro ⟨n, k, m⟩ ⟨n', k', m'⟩ h
    simp only [g, Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have h' := eq_of_heq h
    simp only [Sigma.mk.injEq] at h'
    obtain ⟨rfl, h''⟩ := h'
    have hm := eq_of_heq h''
    obtain rfl : m = m' := funext fun j => funext fun i => hf (congrFun (congrFun hm j) i)
    rfl
  refine ⟨fun G => g (d G).code, fun G G' h => ?_⟩
  obtain ⟨e⟩ := (d G).nonempty_iso_of_code_eq (d G') (hg h)
  exact nonempty_iso_of_over_isTerminal B S hS _ hT e


/-- On the small étale site of an algebraic space, restriction of morphisms to the slice at a
terminal chart is injective. -/
theorem overFunctor_map_injective_of_isTerminal (hT : IsTerminal T)
    {G G' : Modules.{u, u} B S hS F hF} :
    Function.Injective (fun f : G ⟶ G' =>
      (SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) T).map
          f) := by
  have hcov : (smallEtaleRingedSite B S hS F hF).J.CoversTop (fun _ : Unit => T) := fun X => by
    refine (smallEtaleRingedSite B S hS F hF).J.superset_covering ?_
      ((smallEtaleRingedSite B S hS F hF).J.top_mem X)
    rintro Y g -
    exact ⟨(), ⟨hT.from Y⟩⟩
  exact fun _ _ h => Stacks.SheafOfModules.hom_ext_of_coversTop
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) hcov
    fun _ => h

/-- **Morphisms out of a finitely presented quasi-coherent module on the small étale site of an
algebraic space with an affine terminal chart `T` are determined by finitely many sections of the
target over `T`.** -/
theorem exists_injective_hom_of_isTerminal (hT : IsTerminal T)
    (hTa : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj T))
    (G G' : Modules.{u, u} B S hS F hF)
    (hq : G.IsQuasicoherentOnSite) (hfp : SheafOfModules.IsFinitePresentationOnSite G) :
    ∃ (n : ℕ) (w : (G ⟶ G') → (Fin n → G'.val.obj (op T))), Function.Injective w := by
  obtain ⟨d⟩ := SheafOfModules.nonempty_finitePresentationData
    (hasFiniteGlobalPresentation_over_of_isAffine hF hTa G hq hfp)
  obtain ⟨u, hu⟩ := d.exists_injective_hom (G'.over T)
  refine ⟨d.n, fun f i => (u ((SheafOfModules.overFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) T).map f) i).1
      (op (Over.mk (𝟙 T))), ?_⟩
  intro f g h
  refine overFunctor_map_injective_of_isTerminal hF hT (hu (funext fun i => ?_))
  exact SheafOfModules.sections_eval_injective_of_isTerminal Over.mkIdTerminal _ (congrFun h i)

end AlgebraicGeometry.Space

end
