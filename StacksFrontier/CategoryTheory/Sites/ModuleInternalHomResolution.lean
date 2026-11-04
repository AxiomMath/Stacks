module

public import StacksFrontier.CategoryTheory.Sites.ModuleInternalHomLocalExt
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantModules.Morphisms

/-!
# `ℋom_A(G, -)` takes a resolution of a locally injective sheaf to a resolution

Let `(C, K)` be a site and `A` a commutative noetherian ring. Let `G` be a sheaf of `A`-modules
which is locally constant with finitely presented values, and let `ω` be a sheaf of `A`-modules
which is locally isomorphic to the constant sheaf of an injective `A`-module. For a resolution
`ω ⟶ J` concentrated in nonnegative degrees whose modules of sections are injective, the induced
map `ℋom_A(G, ω)[0] ⟶ ℋom_A(G, J)` is a quasi-isomorphism: the local `Ext` sheaves
`ℰxtⁱ_A(G, ω)` vanish for `i > 0`.

The vanishing is local: over a common refinement of the coverings trivializing `G` and `ω`, the
restriction of `ℋom_A(G, J)` is `ℋom_A(M̲, J|)` with `ω|` constant on an injective module
(`Stacks.ConstantSheaf.overPullbackModuleSheafHomIso`), which is
`Stacks.ModuleInternalHom.extVanishes_constantSheaf_of_finite`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe w v u

namespace Stacks.ModuleInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (A : Type w) [CommRing A]

section Local

variable (J : CochainComplex (Sheaf K (ModuleCat.{max u v} A)) ℤ)

/-- `ℋom_A(G, J)|_X ≅ ℋom_A(G|_X, J|_X)`, as complexes. -/
def overPullbackHomComplexIso (X : C) (G : Sheaf K (ModuleCat.{max u v} A)) :
    ((K.overPullback (ModuleCat.{max u v} A) X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (homComplex K A J G) ≅
      homComplex (K.over X) A (((K.overPullback (ModuleCat.{max u v} A) X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) ((K.overPullback (ModuleCat.{max u v} A) X).obj G) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => overPullbackModuleSheafHomIso.{u, v, w, max u v} K A X G (J.X n))
    (fun i j _ => by
      refine Sheaf.hom_ext (NatTrans.ext (funext fun R => ModuleCat.hom_ext (LinearMap.ext
        fun (α : (K.overPullback (ModuleCat.{max u v} A) R.unop.left).obj G ⟶
          (K.overPullback (ModuleCat.{max u v} A) R.unop.left).obj (J.X i)) => ?_)))
      rfl)

variable [Small.{max u v} A] [IsNoetherianRing A] [J.IsStrictlyGE 0]
  {ω : Sheaf K (ModuleCat.{max u v} A)}
  (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω ⟶ J) [QuasiIso ι]
  (hJ : ∀ (n : ℤ) (X : Cᵒᵖ), Module.Injective A ((J.X n).obj.obj X))

/-- `ω` is locally isomorphic to the constant sheaf of an injective `A`-module. -/
def IsLocallyConstantInjective (ω : Sheaf K (ModuleCat.{max u v} A)) : Prop :=
  ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ K U ∧ ∀ i, ∃ E : ModuleCat.{max u v} A, Module.Injective A E ∧
      Nonempty ((constantSheaf (K.over (V i)) (ModuleCat.{max u v} A)).obj E ≅
        (K.overPullback (ModuleCat.{max u v} A) (V i)).obj ω)

include ι hJ in
/-- **Local `Ext` vanishing**: for `G` locally constant with finitely presented values and `ω`
locally constant on an injective module, `ℋⁿ(ℋom_A(G, J)) = 0` for `n > 0`. -/
theorem extVanishes_of_isFinitePresentationLocallyConstant (G : Sheaf K (ModuleCat.{max u v} A))
    (hG : IsFinitePresentationLocallyConstantModuleSheaf K A G)
    (hω : IsLocallyConstantInjective K A ω) : ExtVanishes K A J G := by
  intro n hn
  refine Sheaf.isZero_of_forall_isZero_sections _ fun U => ?_
  obtain ⟨I, V, f, hf, hV⟩ := hG U
  obtain ⟨I', W, g, hg, hW⟩ := hω U
  obtain ⟨Kk, Z, p, hp⟩ := (Sieve.ofArrows V f ⊓ Sieve.ofArrows W g).exists_eq_ofArrows
  refine Sheaf.isZero_sections_of_isZero_sections_of_covering _ (Presieve.ofArrows Z p)
    (by change Sieve.ofArrows Z p ∈ K U; rw [← hp]; exact K.intersection_covering hf hg) ?_
  rintro _ _ ⟨k⟩
  have hk : (Sieve.ofArrows V f ⊓ Sieve.ofArrows W g) (p k) := by
    rw [hp]; exact Sieve.ofArrows_mk Z p k
  obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff V f (p k)).mp hk.1
  obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff W g (p k)).mp hk.2
  obtain ⟨M, hM, ⟨eG⟩⟩ := hV i
  obtain ⟨E, hE, ⟨eω⟩⟩ := hW j
  let eG' := overPullbackIsoOfMapModule K a G M eG
  let eω' := overPullbackIsoOfMapModule K b ω E eω
  have : CochainComplex.IsStrictlyGE (((K.overPullback (ModuleCat.{max u v} A)
      (Z k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact Functor.map_isZero (K.overPullback (ModuleCat.{max u v} A) (Z k))
      (J.isZero_of_isStrictlyGE 0 i hi)
  have : Module.Finite A M := inferInstance
  have key := extVanishes_constantSheaf_of_finite (K.over (Z k)) A
    (((K.overPullback (ModuleCat.{max u v} A) (Z k)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J)
    ((HomologicalComplex.singleMapHomologicalComplex (K.overPullback (ModuleCat.{max u v} A) (Z k))
      (ComplexShape.up ℤ) 0).inv.app ω ≫
      ((K.overPullback (ModuleCat.{max u v} A) (Z k)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ι)
    (fun n W => hJ n (op W.unop.left)) E eω'.symm M n hn
  have hP : IsZero ((K.overPullback (ModuleCat.{max u v} A) (Z k)).obj
      ((homComplex K A J G).homology n)) :=
    key.of_iso ((((homComplex K A J G).sc n).mapHomologyIso
        (K.overPullback (ModuleCat.{max u v} A) (Z k))).symm ≪≫
      HomologicalComplex.homologyMapIso (overPullbackHomComplexIso K A J (Z k) G) n ≪≫
      HomologicalComplex.homologyMapIso (homComplexIso (K.over (Z k)) A _ eG') n)
  exact Functor.map_isZero ((sheafSections (K.over (Z k)) (ModuleCat.{max u v} A)).obj
    (op (Over.mk (𝟙 (Z k))))) hP

include ι hJ in
/-- **`ℋom_A(G, -)` takes a resolution of a locally injective sheaf to a resolution**: for `G`
locally constant with finitely presented values, `ω` locally constant on an injective `A`-module
and `ω ⟶ J` a resolution concentrated in nonnegative degrees with injective modules of sections,
the induced map `ℋom_A(G, ω)[0] ⟶ ℋom_A(G, J)` is a quasi-isomorphism. -/
theorem quasiIso_homFunctor_map (G : Sheaf K (ModuleCat.{max u v} A))
    (hG : IsFinitePresentationLocallyConstantModuleSheaf K A G)
    (hω : IsLocallyConstantInjective K A ω) :
    QuasiIso (((homFunctor K A G).mapHomologicalComplex (ComplexShape.up ℤ)).map ι) := by
  have hzero : ∀ (L : CochainComplex (Sheaf K (ModuleCat.{max u v} A)) ℤ) (n : ℤ),
      IsZero (L.X n) →
      IsZero ((((homFunctor K A G).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology n) :=
    fun L n h => ShortComplex.isZero_homology_of_isZero_X₂ _
      (isZero_moduleSheafHom_of_isZero_right K A G h)
  have hω0 : ∀ n : ℤ, n ≠ 0 → IsZero ((((homFunctor K A G).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω)).homology
        n) := fun n hn => hzero _ n (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  rw [quasiIso_iff]
  intro n
  rcases lt_trichotomy n 0 with hlt | rfl | hgt
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (hω0 n hlt.ne).isIso (hzero J n (J.isZero_of_isStrictlyGE 0 n hlt)) _
  · exact quasiIsoAt_zero_homFunctor_map K A J ι G
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (hω0 n hgt.ne').isIso
      (extVanishes_of_isFinitePresentationLocallyConstant K A J ι hJ G hG hω n hgt) _

end Local

end Stacks.ModuleInternalHom
