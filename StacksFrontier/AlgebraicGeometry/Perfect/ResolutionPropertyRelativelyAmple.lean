module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Generation
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
public import StacksFrontier.AlgebraicGeometry.SectionLift.Basic

/-!
# The resolution property along a morphism carrying a relatively ample module

[Stacks, Tag 0FDD]: if `f : X ⟶ Y` is a morphism of schemes, `Y` is quasi-compact,
quasi-separated and has the resolution property, and some invertible `𝒪_X`-module is ample
relative to `f`, then `X` has the resolution property.

## Main results

* `AlgebraicGeometry.hasResolutionProperty_of_isRelativelyAmple`: the statement.

## Implementation notes

Let `F` be a finite type quasi-coherent `𝒪_X`-module and let `V₁, …, V_m` be a finite affine
open cover of the quasi-compact scheme `Y`, with `U_j = f⁻¹(V_j)`. Relative ampleness makes the
restriction of `L` to each `U_j` ample, so clause (7) of [Stacks, Tag 01Q3]
(`Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple`)
applies on `U_j` and produces, for all sufficiently positive twists, finitely many global
sections of `F|_{U_j} ⊗ (L|_{U_j})^{⊗ n}` generating that module. Because that clause bounds the
degree from below rather than naming one degree, a single `n` works for every `j` — the maximum
over the finitely many `j` — so the whole argument runs with the one `𝒪_Y`-module
`f_*(F ⊗ L^{⊗ n})`. Those sections are sections of `f_*(F ⊗ L^{⊗ n})` over `V_j`;
[Stacks, Tag 01PG], in the form
`Stacks.Tag07RMSectionLift.exists_hom_forall_mem_range_pushforward`, puts all of them inside one
finite type quasi-coherent submodule `E`, the resolution property of `Y` covers `E` by a finite
locally free `E'`, and the transpose along `pullback f ⊣ pushforward f` of the composite
`E' ⟶ E ⟶ f_*(F ⊗ L^{⊗ n})` is an epimorphism `f^*E' ⟶ F ⊗ L^{⊗ n}`. Tensoring with
`L^{⊗ (-n)}`, which is an equivalence of categories, untwists it to an epimorphism from the
finite locally free module `f^*E' ⊗ L^{⊗ (-n)}` onto `F`.

Two comparisons carry the weight of the proof.

* `restrictTwistIso` identifies the restriction of the global twist `F ⊗ L^{⊗ n}` to an open
  with the twist formed on that open, which is what lets the sections produced on `U_j` be read
  as sections of the global module over `U_j`. It is assembled from
  `Scheme.Modules.restrictFunctorIsoPullback`, [Stacks, Tag 01CD] for a morphism of schemes
  (`Stacks.RelativeVeryAmple.pullbackTensorModulesIso`) and
  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`. The last of these is stated for a
  natural number exponent, which costs nothing here: the clause (7) threshold may be raised to a
  nonnegative degree before it is used.
* `epi_of_forall_open_generators` reduces being an epimorphism to the existence, near each
  point, of generating sections of the restriction of the target whose germs lie in the range of
  the stalk map. Only surjectivity — not any statement about spans — crosses the comparison of
  the stalk of a restriction with the stalk of the original module
  (`Scheme.Modules.restrictStalkNatIso`), so no semilinearity over the stalk map of the open
  immersion is needed: the spanning hypothesis is used on the open subscheme, where the two
  stalks carry the same ring.

The germ of a lifted section is placed in the range of the transposed morphism by
`mem_range_stalk_pushforward`, which uses only that an epimorphism is surjective on stalks, that
a stalk element is the germ of a section over some open, and the triangle identity
`φ = unit ≫ f_*(φ')` evaluated on sections. The counit of the adjunction is never evaluated on
a stalk.

Quasi-compactness of `f` is part of relative ampleness, and quasi-separatedness of `f` is not an
extra assumption either: the quasi-separatedness of each `U_j` is the first conjunct of the
clause (7) theorem above, and `quasiSeparatedSpace_of_forall_preimage` assembles those into
quasi-separatedness of `X` itself, whence `QuasiSeparated f`. That assembly is a direct argument
rather than an appeal to locality on the target: for affine opens `A`, `B` of `X` it covers
`A ∩ B` by the finitely many `A ∩ B ∩ U_j` and applies quasi-separatedness of `U_j` to the pair
`A ∩ U_j`, `B ∩ U_j`, whose compactness is `isCompact_inter_preimage` — the morphism
`A ⟶ Y` out of the affine `A` is quasi-compact because `Y` is quasi-separated, so it pulls the
compact open `V_j` back to a compact set. The argument is direct rather than an appeal to
Mathlib's locality of quasi-separatedness on the target, whose carrying instance is not
reachable by instance synthesis at the transparency this context provides.

## References

* [Stacks Project, Tag 0FDD](https://stacks.math.columbia.edu/tag/0FDD)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Ample (IsInvertibleModule tensorPowModule)
open scoped Stacks.ModuleStalk

universe u

namespace AlgebraicGeometry

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X Y : Scheme.{u}}

/-- The restriction to an open subscheme of a twist by a tensor power of an invertible module,
identified with the twist formed on that open subscheme:
`(F ⊗ L^{⊗ k})|_U ≅ F|_U ⊗ (L|_U)^{⊗ k}`. -/
private def restrictTwistIso (U : X.Opens) (F L : X.Modules) [IsInvertibleModule X L] (k : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj (F ⊗ tensorPowModule X L (k : ℤ)) ≅
      ((modulePullback U.ι.toLRSHom.toShHom).obj F) ⊗
        tensorPowModule U.toScheme ((modulePullback U.ι.toLRSHom.toShHom).obj L) (k : ℤ) :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _) ≪≫
    (Scheme.Modules.pullback U.ι).mapIso
      (Stacks.SheafOfModules.tensorObjIso X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F
        (tensorPowModule X L (k : ℤ))) ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorModulesIso U.ι F (tensorPowModule X L (k : ℤ)) ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso U.toScheme (Iso.refl _)
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso U.ι L k) ≪≫
    (Stacks.SheafOfModules.tensorObjIso U.toScheme.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf U.toScheme) _ _).symm

/-- A twist of a quasi-coherent `𝒪_X`-module by a tensor power of an invertible module is
quasi-coherent. -/
private theorem isQuasicoherent_twist (F L : X.Modules) [IsInvertibleModule X L]
    [F.IsQuasicoherent] (n : ℤ) : (F ⊗ tensorPowModule X L n).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Stacks.SheafOfModules.tensorObjIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F
      (tensorPowModule X L n)).symm
    (Scheme.Modules.isQuasicoherent_tensorObj F (tensorPowModule X L n) ‹_›
      (Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L n))

/-- The inverse image of a quasi-coherent `𝒪_X`-module along the inclusion of an open subscheme
is quasi-coherent. -/
private theorem isQuasicoherent_restrictPullback (U : X.Opens) (F : X.Modules)
    [F.IsQuasicoherent] :
    ((modulePullback U.ι.toLRSHom.toShHom).obj F).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F)
    inferInstance

/-- Over the preimage of an affine open of the base, every sufficiently positive twist of a
finite type quasi-coherent module by a module ample relative to `f` is generated by finitely many
sections. -/
private theorem exists_generatingSections (f : X ⟶ Y) (L : X.Modules)
    [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (F : X.Modules)
    [F.IsQuasicoherent] [SheafOfModules.IsFiniteType.{u, u, u} F]
    (V : Y.Opens) (hV : IsAffineOpen V) :
    ∃ n₀ : ℤ, ∀ k : ℕ, n₀ ≤ (k : ℤ) →
      ∃ σ : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj
        (F ⊗ tensorPowModule X L (k : ℤ))).GeneratingSections, Finite σ.I := by
  have hamp := Stacks.RelativeAmple.IsRelativelyAmple.isAmple_preimage f L hL V hV
  have hqc := isQuasicoherent_restrictPullback (f ⁻¹ᵁ V) F
  have hft : SheafOfModules.IsFiniteType.{u, u, u}
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj F) :=
    Stacks.Modules.isFiniteType_pullback (f ⁻¹ᵁ V).ι F ‹_›
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ hamp).2 ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj F) hqc hft
  refine ⟨n₀, fun k hk => ?_⟩
  obtain ⟨σ, hσ⟩ := hn₀ (k : ℤ) hk
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso
    (restrictTwistIso (f ⁻¹ᵁ V) F L k).symm σ, hσ⟩

/-- The stalk map of a morphism of `𝒪_X`-modules carries the germ of a section to the germ of its
image. -/
private theorem stalk_map_germ {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (W : X.Opens) (hx : x ∈ W) (t : Γ(M, W)) :
    ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map φ).hom
        ((TopCat.Presheaf.germ M.presheaf W x hx).hom t) =
      (TopCat.Presheaf.germ N.presheaf W x hx).hom (φ.app W t) := by
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val) _ = _
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val) t

section RestrictStalk

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] {M N : X.Modules} (x : U)

/-- The comparison of the stalk at `x` of the restriction of `M` along an open immersion `j` with
the stalk of `M` at `j x`, as a map of underlying types. -/
private def restrictStalkHom (M : X.Modules) :
    ((SheafOfModules.stalkFunctor U.ringCatSheaf x).obj
        ((Scheme.Modules.restrictFunctor j).obj M) : Type u) →
      ((SheafOfModules.stalkFunctor X.ringCatSheaf (j.base x)).obj M : Type u) :=
  fun z => ((Scheme.Modules.restrictStalkNatIso j x).hom.app M).hom z

/-- The stalk comparison for a restriction along an open immersion is bijective. -/
private theorem bijective_restrictStalkHom (M : X.Modules) :
    Function.Bijective (restrictStalkHom j x M) :=
  ConcreteCategory.bijective_of_isIso ((Scheme.Modules.restrictStalkNatIso j x).hom.app M)

/-- The stalk comparison for a restriction along an open immersion is natural in the module. -/
private theorem restrictStalkHom_naturality (φ : M ⟶ N) (z) :
    restrictStalkHom j x N
        (((SheafOfModules.stalkFunctor U.ringCatSheaf x).map
          ((Scheme.Modules.restrictFunctor j).map φ)).hom z) =
      ((SheafOfModules.stalkFunctor X.ringCatSheaf (j.base x)).map φ).hom
        (restrictStalkHom j x M z) :=
  ConcreteCategory.congr_hom ((Scheme.Modules.restrictStalkNatIso j x).hom.naturality φ) z

/-- The stalk comparison for a restriction along an open immersion carries the germ of a section
over an open to the germ of that section over its image. -/
private theorem restrictStalkHom_germ (M : X.Modules) (W : U.Opens) (hw : x ∈ W)
    (s : Γ((Scheme.Modules.restrictFunctor j).obj M, W)) :
    restrictStalkHom j x M
        ((TopCat.Presheaf.germ ((Scheme.Modules.restrictFunctor j).obj M).val.presheaf W x
          hw).hom s) =
      (TopCat.Presheaf.germ M.presheaf (j ''ᵁ W) (j.base x) (by simpa using hw)).hom s :=
  ConcreteCategory.congr_hom
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x M (U := W) hw) s

/-- A morphism of `𝒪_X`-modules surjective on the stalk at `x` of its restriction along an open
immersion is surjective on the stalk at the image of `x`. -/
private theorem surjective_stalk_of_restrict (φ : M ⟶ N)
    (h : Function.Surjective ((SheafOfModules.stalkFunctor U.ringCatSheaf x).map
            ((Scheme.Modules.restrictFunctor j).map φ)).hom) :
    Function.Surjective ((SheafOfModules.stalkFunctor X.ringCatSheaf (j.base x)).map φ).hom := by
  intro y
  obtain ⟨ζ, hζ⟩ := (bijective_restrictStalkHom j x N).2 y
  obtain ⟨ξ, hξ⟩ := h ζ
  exact ⟨restrictStalkHom j x M ξ, by
    rw [← restrictStalkHom_naturality j x φ ξ, hξ, hζ]⟩

/-- A stalk element whose comparison image lies in the range of the stalk map of `φ` lies in the
range of the stalk map of the restriction of `φ` along an open immersion. -/
private theorem mem_range_restrict_of_mem_range (φ : M ⟶ N) (w) (h : restrictStalkHom j x N w ∈
      Set.range ((SheafOfModules.stalkFunctor X.ringCatSheaf (j.base x)).map φ).hom) :
    w ∈ Set.range ((SheafOfModules.stalkFunctor U.ringCatSheaf x).map
      ((Scheme.Modules.restrictFunctor j).map φ)).hom := by
  obtain ⟨η, hη⟩ := h
  obtain ⟨ξ, hξ⟩ := (bijective_restrictStalkHom j x M).2 η
  refine ⟨ξ, (bijective_restrictStalkHom j x N).1 ?_⟩
  rw [restrictStalkHom_naturality j x φ ξ, hξ, hη]

/-- A section of `N` over the image of an open whose germ lies in the range of the stalk map of
`φ` has, read as a section of the restriction of `N`, its germ in the range of the stalk map of
the restriction of `φ`. -/
private theorem mem_range_restrict_germ (φ : M ⟶ N) (W : U.Opens) (hw : x ∈ W)
    (s : Γ((Scheme.Modules.restrictFunctor j).obj N, W))
    (h : (TopCat.Presheaf.germ N.presheaf (j ''ᵁ W) (j.base x) (by simpa using hw)).hom s ∈
      Set.range ((SheafOfModules.stalkFunctor X.ringCatSheaf (j.base x)).map φ).hom) :
    (TopCat.Presheaf.germ ((Scheme.Modules.restrictFunctor j).obj N).val.presheaf W x hw).hom s ∈
      Set.range ((SheafOfModules.stalkFunctor U.ringCatSheaf x).map
        ((Scheme.Modules.restrictFunctor j).map φ)).hom :=
  mem_range_restrict_of_mem_range j x φ _ (by rw [restrictStalkHom_germ]; exact h)

end RestrictStalk

/-- A morphism of sheaves of modules whose stalk map at a point has in its range a family of
germs of global sections spanning that stalk is surjective there. -/
private theorem surjective_stalk_of_span {Z : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) {A B : SheafOfModules.{u} O}
    (ψ : A ⟶ B) {I : Type u} (s : I → B.sections) (z : Z)
    (hs : Submodule.span (R := (TopCat.Presheaf.stalk O.obj z : RingCat))
        (Set.range fun i ↦ (TopCat.Presheaf.germ B.val.presheaf ⊤ z (by trivial)).hom
          ((s i).eval (Opposite.op ⊤))) = ⊤)
    (hmem : ∀ i, (TopCat.Presheaf.germ B.val.presheaf ⊤ z (by trivial)).hom
          ((s i).eval (Opposite.op ⊤)) ∈
        Set.range ((SheafOfModules.stalkFunctor O z).map ψ).hom) :
    Function.Surjective ((SheafOfModules.stalkFunctor O z).map ψ).hom := by
  refine LinearMap.range_eq_top.mp (top_le_iff.mp (hs.ge.trans (Submodule.span_le.mpr ?_)))
  rintro _ ⟨i, rfl⟩
  exact hmem i

/-- The stalk map of a composite of morphisms of `𝒪_X`-modules is the composite of the stalk
maps. -/
private theorem stalk_map_comp {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P) (x : X) (z) :
    ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map (a ≫ b)).hom z =
      ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map b).hom
        (((SheafOfModules.stalkFunctor X.ringCatSheaf x).map a).hom z) :=
  ConcreteCategory.congr_hom ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map_comp a b) z

/-- A morphism of `𝒪_X`-modules commutes with restriction of sections to a smaller open. -/
private theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V)
    (t : Γ(M, V)) : N.presheaf.map i.op (φ.app V t) = φ.app U (M.presheaf.map i.op t) :=
  (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) t).symm

/-- For an epimorphism `q` of `𝒪_Y`-modules and `e : E ⟶ f_*G`, the germ at a point of `X` of a
section of `G` in the image of `e` lies in the range of the stalk map of the transpose of `q ≫ e`
along `pullback f ⊣ pushforward f`. -/
private theorem mem_range_stalk_pushforward (f : X ⟶ Y) {E' E : Y.Modules} {G : X.Modules}
    (q : E' ⟶ E) [Epi q] (e : E ⟶ (Scheme.Modules.pushforward f).obj G)
    (V : Y.Opens) (a : Γ(E, V)) (x : X) (hx : f.base x ∈ V) :
    (TopCat.Presheaf.germ G.presheaf (f ⁻¹ᵁ V) x hx).hom (e.app V a) ∈
      Set.range ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map
        (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E' G).symm (q ≫ e))).hom := by
  have hunit : q ≫ e = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E' ≫
      (Scheme.Modules.pushforward f).map
        (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E' G).symm (q ≫ e)) := by
    exact (Equiv.apply_symm_apply _ _).symm.trans (Adjunction.homEquiv_unit _ _ _ _)
  obtain ⟨b, hb⟩ := (epi_iff_stalk_surjective Y.ringCatSheaf q).mp ‹Epi q› (f.base x)
      ((TopCat.Presheaf.germ E.presheaf V (f.base x) hx).hom a)
  obtain ⟨W, hyW, a', ha'⟩ := TopCat.Presheaf.exists_germ_eq E'.presheaf b
  have h1 : (TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj G).presheaf W
          (f.base x) hyW).hom ((q ≫ e).app W a') =
      (TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj G).presheaf V
          (f.base x) hx).hom (e.app V a) :=
    (stalk_map_germ (q ≫ e) (f.base x) W hyW a').symm.trans
      ((stalk_map_comp q e (f.base x)
          ((TopCat.Presheaf.germ E'.presheaf W (f.base x) hyW).hom a')).trans
        ((congrArg (fun w =>
              ((SheafOfModules.stalkFunctor Y.ringCatSheaf (f.base x)).map e).hom w)
            ((congrArg (fun w =>
              ((SheafOfModules.stalkFunctor Y.ringCatSheaf (f.base x)).map q).hom w)
              ha').trans hb)).trans (stalk_map_germ e (f.base x) V hx a)))
  obtain ⟨W', hyW', iW, iV, heq⟩ := TopCat.Presheaf.germ_eq
    ((Scheme.Modules.pushforward f).obj G).presheaf (f.base x) hyW hx
    ((q ≫ e).app W a') (e.app V a) h1
  rw [app_naturality (q ≫ e) iW a'] at heq
  refine ⟨(TopCat.Presheaf.germ ((Scheme.Modules.pullback f).obj E').presheaf (f ⁻¹ᵁ W') x
    hyW').hom (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E').app W'
      (E'.presheaf.map iW.op a')), ?_⟩
  rw [stalk_map_germ _ x (f ⁻¹ᵁ W') hyW'
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E').app W'
      (E'.presheaf.map iW.op a'))]
  have h2 : (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E' G).symm
        (q ≫ e)).app (f ⁻¹ᵁ W')
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E').app W'
          (E'.presheaf.map iW.op a')) =
      (q ≫ e).app W' (E'.presheaf.map iW.op a') :=
    (congrArg (fun ψ => Scheme.Modules.Hom.app ψ W' (E'.presheaf.map iW.op a')) hunit).symm
  rw [h2, heq]
  exact TopCat.Presheaf.germ_res_apply G.presheaf
    ((TopologicalSpace.Opens.map f.base).map iV) x hyW' (e.app V a)

/-- A morphism of `𝒪_X`-modules surjective on every stalk is an epimorphism. -/
private theorem epi_of_stalk_surjective {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, Function.Surjective
      ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map φ).hom) : Epi φ :=
  (epi_iff_stalk_surjective X.ringCatSheaf φ).mpr h

/-- A morphism of `𝒪_X`-modules is an epimorphism as soon as every point has an open
neighbourhood over which the target is generated by sections whose germs lie in the range of the
stalk map. -/
private theorem epi_of_forall_open_generators {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ (W : X.Opens) (hx : x ∈ W)
      (σ : ((Scheme.Modules.restrictFunctor W.ι).obj N).GeneratingSections), ∀ i,
        (TopCat.Presheaf.germ N.presheaf (W.ι ''ᵁ ⊤) x
            (by rw [Scheme.Opens.ι_image_top]; exact hx)).hom ((σ.s i).eval (Opposite.op ⊤)) ∈
          Set.range ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map φ).hom) :
    Epi φ := by
  refine epi_of_stalk_surjective φ fun x => ?_
  obtain ⟨W, hx, σ, hmem⟩ := h x
  refine surjective_stalk_of_restrict W.ι (⟨x, hx⟩ : W.toScheme) φ ?_
  refine surjective_stalk_of_span W.toScheme.ringCatSheaf _ σ.s (⟨x, hx⟩ : W.toScheme)
    ((freeHom_stalk_surjective_iff_span W.toScheme.ringCatSheaf
      ((Scheme.Modules.restrictFunctor W.ι).obj N) σ.s (⟨x, hx⟩ : W.toScheme)).mp
      ((epi_iff_stalk_surjective _ _).mp σ.epi _)) fun i => ?_
  exact mem_range_restrict_germ W.ι (⟨x, hx⟩ : W.toScheme) φ ⊤ trivial _ (hmem i)

/-- The inverse image of a finite locally free module, twisted by a tensor power of an invertible
module, is finite locally free. -/
private theorem isFiniteLocallyFree_pullbackTensor (f : X ⟶ Y) (E' : Y.Modules)
    (hE' : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E')
    (L : X.Modules) [IsInvertibleModule X L] (n : ℤ) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (((Scheme.Modules.pullback f).obj E' ⊗ tensorPowModule X L n : X.Modules)) := by
  have h1 : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf)
      ((Scheme.Modules.pullback f).obj E') :=
    SheafOfModules.IsFiniteLocallyFree.pullback_scheme f E' hE'
  have h2 : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (tensorPowModule X L n) :=
    haveI := Stacks.Ample.isInvertibleModule_tensorPowModule X L n
    haveI := Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
      X (tensorPowModule X L n)
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (tensorPowModule X L n) 1
  exact SheafOfModules.IsFiniteLocallyFree.of_iso
    (h := (isFiniteLocallyFree_tensorObj (hM := h1) (hN := h2) _ _))
    (Stacks.SheafOfModules.tensorObjIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _ _).symm

/-- The intersection of an affine open of `X` with the preimage of a compact open of a
quasi-separated base along a quasi-compact morphism is compact. -/
private theorem isCompact_inter_preimage (f : X ⟶ Y) [QuasiSeparatedSpace Y] [QuasiCompact f]
    (A : X.affineOpens) (V : Y.Opens) (hV : IsCompact (V : Set Y)) :
    IsCompact (((A : X.Opens) : Set X) ∩ ((f ⁻¹ᵁ V : X.Opens) : Set X)) := by
  have hA := A.2
  have hcs : CompactSpace (A : X.Opens).toScheme := inferInstance
  have h1 : IsCompact (((A : X.Opens).ι ≫ f).base ⁻¹' (V : Set Y)) :=
    QuasiCompact.isCompact_preimage (f := (A : X.Opens).ι ≫ f) _ V.isOpen hV
  have hsub : ((A : X.Opens) : Set X) ∩ ((f ⁻¹ᵁ V : X.Opens) : Set X) ⊆
      Set.range (A : X.Opens).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact Set.inter_subset_left
  have hpre : (A : X.Opens).ι.base ⁻¹'
        (((A : X.Opens) : Set X) ∩ ((f ⁻¹ᵁ V : X.Opens) : Set X)) =
      ((A : X.Opens).ι ≫ f).base ⁻¹' (V : Set Y) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_inter_iff, Scheme.Hom.comp_base, TopCat.comp_app,
      SetLike.mem_coe, TopologicalSpace.Opens.map_coe, and_iff_right_iff_imp]
    exact fun _ => w.2
  have h2 := ((A : X.Opens).ι.isOpenEmbedding.isEmbedding.isCompact_iff
    (s := (A : X.Opens).ι.base ⁻¹'
      (((A : X.Opens) : Set X) ∩ ((f ⁻¹ᵁ V : X.Opens) : Set X)))).mp (by rw [hpre]; exact h1)
  rwa [Set.image_preimage_eq_of_subset hsub] at h2

/-- The source of a quasi-compact morphism to a quasi-compact, quasi-separated scheme is
quasi-separated as soon as the preimage of every affine open of the target is. -/
private theorem quasiSeparatedSpace_of_forall_preimage (f : X ⟶ Y) [CompactSpace Y]
    [QuasiSeparatedSpace Y] [QuasiCompact f]
    (h : ∀ V : Y.affineOpens, QuasiSeparatedSpace (f ⁻¹ᵁ (V : Y.Opens)).toScheme) :
    QuasiSeparatedSpace X := by
  obtain ⟨t, ht⟩ := Y.isBasis_affineOpens.isOpenCover.exists_finite_of_compactSpace
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro A B
  have hcov : ((A : X.Opens) : Set X) ∩ ((B : X.Opens) : Set X) =
      ⋃ V ∈ (t : Set Y.affineOpens),
        (((A : X.Opens) : Set X) ∩ ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X)) ∩
          (((B : X.Opens) : Set X) ∩ ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X)) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hzA, hzB⟩
      obtain ⟨V, hV⟩ := ht.exists_mem (f.base z)
      exact ⟨V.1, V.2, ⟨hzA, hV⟩, ⟨hzB, hV⟩⟩
    · rintro ⟨V, -, ⟨hzA, -⟩, ⟨hzB, -⟩⟩
      exact ⟨hzA, hzB⟩
  rw [hcov]
  refine t.finite_toSet.isCompact_biUnion fun V _ => ?_
  refine (isQuasiSeparated_iff_quasiSeparatedSpace _
    (f ⁻¹ᵁ (V : Y.Opens) : X.Opens).isOpen).mpr (h V) _ _ Set.inter_subset_right
    ((A : X.Opens).isOpen.inter (f ⁻¹ᵁ (V : Y.Opens) : X.Opens).isOpen)
    (isCompact_inter_preimage f A _ V.2.isCompact) Set.inter_subset_right
    ((B : X.Opens).isOpen.inter (f ⁻¹ᵁ (V : Y.Opens) : X.Opens).isOpen)
    (isCompact_inter_preimage f B _ V.2.isCompact)

/-- A morphism of schemes carrying a relatively ample invertible module onto a quasi-compact,
quasi-separated scheme is quasi-separated. -/
private theorem quasiSeparated_of_isRelativelyAmple (f : X ⟶ Y) [CompactSpace Y]
    [QuasiSeparatedSpace Y] (L : X.Modules) [IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) : QuasiSeparated f :=
  haveI : QuasiCompact f := Stacks.RelativeAmple.IsRelativelyAmple.quasiCompact f L hL
  haveI := quasiSeparatedSpace_of_forall_preimage f fun V =>
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ (Stacks.RelativeAmple.IsRelativelyAmple.isAmple_preimage f L hL V.1 V.2)).1
  QuasiSeparated.of_quasiSeparatedSpace f

/-- **Stacks Tag 0FDD.** If `f : X ⟶ Y` is a morphism of schemes, `Y` is quasi-compact,
quasi-separated and has the resolution property, and `L` is an invertible `𝒪_X`-module ample
relative to `f`, then `X` has the resolution property. -/
@[stacks 0FDD]
theorem hasResolutionProperty_of_isRelativelyAmple {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [HasResolutionProperty Y]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) : HasResolutionProperty X := by
  have : QuasiCompact f := Stacks.RelativeAmple.IsRelativelyAmple.quasiCompact f L hL
  have : QuasiSeparated f := quasiSeparated_of_isRelativelyAmple f L hL
  constructor
  intro F _ _
  obtain ⟨t, ht⟩ := Y.isBasis_affineOpens.isOpenCover.exists_finite_of_compactSpace
  set J := {i : Y.affineOpens // i ∈ t}
  set V : J → Y.affineOpens := fun i => i.1
  choose n₀ hn₀ using fun j : J => exists_generatingSections f L hL F (V j).1 (V j).2
  obtain ⟨m, hm⟩ := Finite.exists_le n₀
  set k : ℕ := (max m 0).toNat
  have hkz : ((k : ℤ)) = max m 0 := Int.toNat_of_nonneg (le_max_right m 0)
  have hkj : ∀ j, n₀ j ≤ (k : ℤ) := fun j => hkz ▸ (hm j).trans (le_max_left m 0)
  choose σ hσ using fun j => hn₀ j k (hkj j)
  have : (F ⊗ tensorPowModule X L (k : ℤ)).IsQuasicoherent := isQuasicoherent_twist F L (k : ℤ)
  have hfinI : ∀ j, Finite (σ j).I := hσ
  have : Finite ((j : J) × (σ j).I) := inferInstance
  obtain ⟨E, hEqc, hEft, e, -, hrange⟩ :=
    Stacks.Tag07RMSectionLift.exists_hom_forall_mem_range_pushforward f
      (F ⊗ tensorPowModule X L (k : ℤ)) (fun p : (j : J) × (σ j).I => V p.1)
      (fun p => (F ⊗ tensorPowModule X L (k : ℤ)).presheaf.map
        (eqToHom (Scheme.Opens.ι_image_top (f ⁻¹ᵁ (V p.1).1)).symm).op
        (((σ p.1).s p.2).eval (Opposite.op ⊤)))
  have := hEqc
  have := hEft
  obtain ⟨E', hE'flf, q, hq⟩ := HasResolutionProperty.exists_finiteLocallyFree_quotient E
  have : Epi q := hq
  have hepi : Epi (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E'
      (F ⊗ tensorPowModule X L (k : ℤ))).symm (q ≫ e)) := by
    refine epi_of_forall_open_generators _ fun x => ?_
    obtain ⟨j, hj⟩ := ht.exists_mem (f.base x)
    refine ⟨f ⁻¹ᵁ (V j).1, hj, σ j, fun i => ?_⟩
    obtain ⟨a, ha⟩ := hrange ⟨j, i⟩
    have hmem := mem_range_stalk_pushforward f q e (V j).1 a x hj
    rw [ha] at hmem
    exact TopCat.Presheaf.germ_res_apply (F ⊗ tensorPowModule X L (k : ℤ)).presheaf
      (eqToHom (Scheme.Opens.ι_image_top (f ⁻¹ᵁ (V j).1)).symm) x hj
      (((σ j).s i).eval (Opposite.op ⊤)) ▸ hmem
  exact ⟨(Scheme.Modules.pullback f).obj E' ⊗ tensorPowModule X L (-(k : ℤ)),
    isFiniteLocallyFree_pullbackTensor f E' hE'flf L (-(k : ℤ)),
    (tensorRight (tensorPowModule X L (-(k : ℤ)))).map _ ≫
      (Stacks.AmpleGlobalGeneration.twistCancelIso L F (k : ℤ)).hom,
    epi_comp' (Stacks.AmpleEventualGeneration.epi_map_tensorRight _ _ hepi) inferInstance⟩

end AlgebraicGeometry

end
