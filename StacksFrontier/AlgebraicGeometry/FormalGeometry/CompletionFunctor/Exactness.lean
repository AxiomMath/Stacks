module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicArtinRees
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Abelian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksCore.Tactic.StacksAttribute

/-!
# The completion functor is exact

Let `X` be a Noetherian scheme and `I` a quasi-coherent sheaf of ideals on `X`. The completion
functor `Coh(𝒪_X) ⥤ Coh(X, I)`, `F ↦ (F / I ⁿ F)`, of Stacks 0880 is exact.

Right exactness is the universal property of the quotients: a map out of `F ^ ∧` is a map of `F`
into the inverse limit of the target, so completion carries the cokernel of a morphism of
coherent modules to the cokernel of its completion.

Left exactness is Artin–Rees. Over an affine open `U` the projection of `F` onto the `n`-th term
of its completion is surjective with kernel `I(U) ⁿ⁺¹ Γ(F, U)`, so a section of that term lifts
to a section `s` of `F`; if the completion of a monomorphism `F ⟶ G` kills the section at level
`n + c`, then the image of `s` lies in `I(U) ^ (n + c + 1) Γ(G, U)`, and the Artin–Rees constant
`c` of `Γ(F, U) ⊆ Γ(G, U)` puts `s` in `I(U) ⁿ⁺¹ Γ(F, U)`, so the section already dies at level
`n`. Since the transition maps of a coherent adic system are epimorphisms, this makes every
component of a morphism annihilated by the completed monomorphism vanish.

## Main results

* `Stacks.Algebraization.completionFunctor_preservesFiniteColimits` — completion is right exact.
* `Stacks.Algebraization.completionFunctor_preservesMonomorphisms` — completion preserves
  monomorphisms.
* `Stacks.Algebraization.completionFunctor_exact` — **Stacks 0881: the completion functor is
  exact.**

## Implementation notes

The Artin–Rees constant is chosen after the affine open, so no constant uniform over all affine
opens is needed: a morphism of sheaves of modules killing the sections over every affine open is
zero, and for a fixed affine open the level at which a section already dies may depend on that
open. This replaces the stalkwise form of the same argument, which would additionally need the
ideal-power multiples of a module to commute with stalks.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared instances, so an epimorphism or a monomorphism found for
one is not found for the other; `epi_scheme_modules` and `mono_scheme_modules` transport them,
the action on sections is always written as `Scheme.Modules.Hom.app`, and the steps that would
naturally be `rw` are `congrArg` against a stated equality of morphisms, as elsewhere in this
subtree.

## References

* [Stacks Project, Tag 0881](https://stacks.math.columbia.edu/tag/0881)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### Transport across the two presentations of the category of modules -/

/-! The zero morphism out of a sheaf of modules presented without `Scheme.Modules` is supplied by
the `local instance` of `CoherentAdicSystem.PullbackIdealPower`, reactivated here rather than
restated: instance search does not see through `AlgebraicGeometry.Scheme.Modules`, a semireducible
definition, to find the zero morphisms of `X.Modules` for a source presented as a bare
`SheafOfModules X.ringCatSheaf`. -/

attribute [local instance] zeroHomOfSheafOfModules

/-- An epimorphism of sheaves of modules on a scheme is one in the `Scheme.Modules`
presentation. -/
private theorem epi_scheme_modules {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (hf : Epi (C := SheafOfModules.{u} X.ringCatSheaf) f) : Epi (C := X.Modules) f :=
  ⟨fun _ _ hh => (cancel_epi (C := SheafOfModules.{u} X.ringCatSheaf) f).1 hh⟩

/-- A monomorphism of sheaves of modules on a scheme is one in the `Scheme.Modules`
presentation. -/
private theorem mono_scheme_modules {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (hf : Mono (C := SheafOfModules.{u} X.ringCatSheaf) f) : Mono (C := X.Modules) f :=
  ⟨fun _ _ hh => (cancel_mono (C := SheafOfModules.{u} X.ringCatSheaf) f).1 hh⟩

/-- The inclusion of the coherent modules on a scheme into all sheaves of modules preserves
finite limits: the coherent modules are a weak Serre subcategory. -/
private theorem coherentInclusion_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits
      (ObjectProperty.ι (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)) :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion of the coherent modules on a scheme into all sheaves of modules preserves
finite colimits. -/
private theorem coherentInclusion_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits
      (ObjectProperty.ι (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)) :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

/-- A monomorphism of coherent modules is a monomorphism of the underlying sheaves of
modules. -/
private theorem mono_hom_of_mono {X : Scheme.{u}}
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (f : F ⟶ G)
    (hf : Mono f) : Mono (C := X.Modules) f.hom := by
  have _ := hf
  have _ := coherentInclusion_preservesFiniteLimits X
  exact mono_scheme_modules _ (preserves_mono_of_preservesLimit
    (ObjectProperty.ι (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)) f)

/-- The quotient projection onto a cokernel of coherent modules is an epimorphism of the
underlying sheaves of modules. -/
private theorem epi_cokernelπ_hom {X : Scheme.{u}}
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (f : F ⟶ G) :
    Epi (C := X.Modules) (cokernel.π f).hom := by
  have _ := coherentInclusion_preservesFiniteColimits X
  exact epi_scheme_modules _ (preserves_epi_of_preservesColimit
    (ObjectProperty.ι (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent))
    (cokernel.π f))

/-- The action of a morphism of modules on sections, in its two spellings. -/
private theorem app_eq_val_app {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (s : Γ(M, U)) : Scheme.Modules.Hom.app φ U s = (φ.val.app (op U)) s := rfl

/-! ### Vanishing of a morphism may be checked on affine opens -/

/-- A morphism of sheaves of modules on a scheme which kills the sections over every affine open
is zero: the affine opens form a basis, so every germ of a value of the morphism is already a
germ of a value over an affine open. -/
public theorem hom_eq_zero_of_affineOpens_app {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (U : X.affineOpens) (s : Γ(M, U.1)), φ.app U.1 s = 0) : φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  show φ.app V s = 0
  refine TopCat.Presheaf.section_ext
    (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab.{u} X) V (φ.app V s) 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := V) hx
  have hnat : φ.app W (M.presheaf.map (homOfLE hWV).op s) =
      N.presheaf.map (homOfLE hWV).op (φ.app V s) :=
    congrArg (fun k => k s) (φ.mapPresheaf.naturality (homOfLE hWV).op)
  have hres : N.presheaf.map (homOfLE hWV).op (φ.app V s) = 0 :=
    hnat.symm.trans (h ⟨W, hW⟩ _)
  have hgerm := TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE hWV) x hxW (φ.app V s)
  rw [hres] at hgerm
  exact hgerm.symm.trans (by simp)

/-! ### Sections of the completion over an affine open -/

/-- **Stacks 0880.** Over an affine open, a section of a coherent module dies in the `n`-th term
of its completion exactly when it is a section of `I ⁿ⁺¹ F`. -/
public theorem completionProjection_app_eq_zero_iff (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (U : X.affineOpens) (s : Γ(F.obj, U.1)) :
    Scheme.Modules.Hom.app (completionProjection X I F n) U.1 s = 0 ↔
      s ∈ (idealPowerMultiple I (n + 1) F.obj).toSubmodule.obj (op U.1) := by
  have _ : F.obj.IsCoherent := F.property
  have _ : F.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F.obj).1
  rw [idealPowerMultiple_toSubmodule_obj_affine I (n + 1) F.obj U,
    ← completionProjection_app_ker X I F n U]
  exact Iff.rfl

/-! ### Right exactness -/

section RightExact

variable (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData)

/-- **The completion functor of Stacks 0880 preserves zero morphisms.** Its components are
determined by their composites with the projections out of the source, which are epimorphisms. -/
public instance completionFunctor_preservesZeroMorphisms :
    (completionFunctor X I).PreservesZeroMorphisms where
  map_zero F G := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
    have hepi := epi_completionProjection X I F n.unop
    refine (@cancel_epi _ _ _ _ _ (completionProjection X I F n.unop) hepi _ _).mp ?_
    have key : completionProjection X I F n.unop ≫
        ((completionFunctor X I).map (0 : F ⟶ G)).hom.app n =
          (0 : F ⟶ G).hom ≫ completionProjection X I G n.unop :=
      completionFunctor_map_quotient X I (0 : F ⟶ G) n.unop
    refine key.trans ?_
    exact (zero_comp (C := X.Modules)).trans (comp_zero (C := X.Modules)).symm

/-- The completion of an epimorphism of coherent modules is an epimorphism: its components are
determined by their composites with the projections, which are epimorphisms. -/
public theorem epi_completionFunctor_map
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (f : F ⟶ G)
    (hf : Epi (C := X.Modules) f.hom) : Epi ((completionFunctor X I).map f) := by
  refine ⟨fun {S} a b hab => ?_⟩
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  have hepi := epi_completionProjection X I G n.unop
  refine (@cancel_epi _ _ _ _ _ (completionProjection X I G n.unop) hepi _ _).mp ?_
  refine (@cancel_epi _ _ _ _ _ f.hom hf _ _).mp ?_
  have key : completionProjection X I F n.unop ≫
      ((completionFunctor X I).map f).hom.app n = f.hom ≫ completionProjection X I G n.unop :=
    completionFunctor_map_quotient X I f n.unop
  calc f.hom ≫ completionProjection X I G n.unop ≫ a.hom.app n
      = (f.hom ≫ completionProjection X I G n.unop) ≫ a.hom.app n := (Category.assoc _ _ _).symm
    _ = (completionProjection X I F n.unop ≫
          ((completionFunctor X I).map f).hom.app n) ≫ a.hom.app n :=
        congrArg (fun z => z ≫ a.hom.app n) key.symm
    _ = completionProjection X I F n.unop ≫
          ((completionFunctor X I).map f).hom.app n ≫ a.hom.app n := Category.assoc _ _ _
    _ = completionProjection X I F n.unop ≫
          ((completionFunctor X I).map f).hom.app n ≫ b.hom.app n :=
        congrArg (fun z => completionProjection X I F n.unop ≫ z)
          (congrArg (fun k : (completionFunctor X I).obj F ⟶ S => k.hom.app n) hab)
    _ = (completionProjection X I F n.unop ≫
          ((completionFunctor X I).map f).hom.app n) ≫ b.hom.app n := (Category.assoc _ _ _).symm
    _ = (f.hom ≫ completionProjection X I G n.unop) ≫ b.hom.app n :=
        congrArg (fun z => z ≫ b.hom.app n) key
    _ = f.hom ≫ completionProjection X I G n.unop ≫ b.hom.app n := Category.assoc _ _ _

/-- **The completion functor of Stacks 0880 preserves cokernels.** A map out of the completion of
a coherent module is a map of that module into the inverse limit of the target, by
`Stacks.Algebraization.completionHomLimitEquiv`, and the cokernel of a morphism of coherent
modules is its cokernel as a sheaf of modules; so a map out of the completion of the source which
kills the completion of the morphism descends to the completion of the cokernel. -/
public theorem completionFunctor_preservesCokernel
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (f : F ⟶ G) :
    PreservesColimit (parallelPair f 0) (completionFunctor X I) := by
  have _ := coherentInclusion_preservesFiniteColimits X
  have _ := epi_completionFunctor_map X I (cokernel.π f) (epi_cokernelπ_hom f)
  have hc := isColimitOfHasCokernelOfPreservesColimit
    (ObjectProperty.ι (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)) f
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f) ?_
  refine (CokernelCofork.isColimitMapCoconeEquiv _ (completionFunctor X I)).2 ?_
  have hw : (completionFunctor X I).map f ≫ (completionFunctor X I).map (cokernel.π f) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  refine CokernelCofork.IsColimit.ofπ' _ hw ?_
    (hp := epi_completionFunctor_map X I (cokernel.π f) (epi_cokernelπ_hom f))
  intro S g hg
  have hz (n : ℕᵒᵖ) : f.hom ≫ adicSystemToHom G S g ≫ limit.π (C := X.Modules) S.obj n = 0 := by
    calc f.hom ≫ adicSystemToHom G S g ≫ limit.π (C := X.Modules) S.obj n
        = f.hom ≫ completionProjection X I G n.unop ≫ g.hom.app n :=
          congrArg (fun z => f.hom ≫ z) (adicSystemToHom_π G S g n)
      _ = (f.hom ≫ completionProjection X I G n.unop) ≫ g.hom.app n :=
          (Category.assoc _ _ _).symm
      _ = (completionProjection X I F n.unop ≫
            ((completionFunctor X I).map f).hom.app n) ≫ g.hom.app n :=
          congrArg (fun z => z ≫ g.hom.app n) (completionFunctor_map_quotient X I f n.unop).symm
      _ = completionProjection X I F n.unop ≫
            ((completionFunctor X I).map f).hom.app n ≫ g.hom.app n := Category.assoc _ _ _
      _ = 0 := (congrArg (fun z => completionProjection X I F n.unop ≫ z)
          (congrArg (fun k : (completionFunctor X I).obj F ⟶ S => k.hom.app n) hg)).trans comp_zero
  have hz' : f.hom ≫ adicSystemToHom G S g = 0 :=
    limit.hom_ext (C := X.Modules) fun n =>
      ((Category.assoc _ _ _).trans (hz n)).trans zero_comp.symm
  obtain ⟨d, hd0⟩ := CokernelCofork.IsColimit.desc' hc (adicSystemToHom G S g) hz'
  have hd : (cokernel.π f).hom ≫ d = adicSystemToHom G S g := hd0
  refine ⟨homToAdicSystem (cokernel f) S d, ?_⟩
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  have hepi := epi_completionProjection X I G n.unop
  refine (@cancel_epi _ _ _ _ _ (completionProjection X I G n.unop) hepi _ _).mp ?_
  calc completionProjection X I G n.unop ≫
        ((completionFunctor X I).map (cokernel.π f)).hom.app n ≫
          (homToAdicSystem (cokernel f) S d).hom.app n
      = (completionProjection X I G n.unop ≫
          ((completionFunctor X I).map (cokernel.π f)).hom.app n) ≫
            (homToAdicSystem (cokernel f) S d).hom.app n := (Category.assoc _ _ _).symm
    _ = ((cokernel.π f).hom ≫ completionProjection X I (cokernel f) n.unop) ≫
          (homToAdicSystem (cokernel f) S d).hom.app n :=
        congrArg (fun z => z ≫ (homToAdicSystem (cokernel f) S d).hom.app n)
          (completionFunctor_map_quotient X I (cokernel.π f) n.unop)
    _ = (cokernel.π f).hom ≫ completionProjection X I (cokernel f) n.unop ≫
          (homToAdicSystem (cokernel f) S d).hom.app n := Category.assoc _ _ _
    _ = completionProjection X I G n.unop ≫ g.hom.app n :=
        (congrArg (fun z => (cokernel.π f).hom ≫ z)
            (completionProjection_homToAdicSystem (cokernel f) S d n)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ limit.π (C := X.Modules) S.obj n) hd).trans
              (adicSystemToHom_π G S g n)))

/-- **The completion functor of Stacks 0880 is right exact.** It preserves zero morphisms and
cokernels, and both categories are abelian. -/
public theorem completionFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (completionFunctor X I) :=
  have _ : HasBinaryBiproducts (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have _ {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (f : F ⟶ G) :
      PreservesColimit (parallelPair f 0) (completionFunctor X I) :=
    completionFunctor_preservesCokernel X I f
  (completionFunctor X I).preservesFiniteColimits_of_preservesCokernels

end RightExact

/-! ### Left exactness -/

section LeftExact

variable (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData)

/-- **The completion functor of Stacks 0880 preserves monomorphisms.**

Fix an affine open `U` and a level `n`, and let `c` be an Artin–Rees constant for
`Γ(F, U) ⊆ Γ(G, U)` along `I(U)`. A section of the `n`-th term of a coherent adic system `S`
mapping to `F ^ ∧` lifts along the transition from level `n + c`, which is an epimorphism; its
image in `(F ^ ∧)_{n+c}` lifts to a section `s` of `F`, whose image in `G` is killed by the
projection onto `(G ^ ∧)_{n+c}` and therefore lies in `I(U) ^ (n + c + 1) Γ(G, U)`. Artin–Rees
puts `s` in `I(U) ⁿ⁺¹ Γ(F, U)`, the kernel of the projection onto `(F ^ ∧)_n`, so the original
section dies at level `n`. -/
public instance completionFunctor_preservesMonomorphisms :
    (completionFunctor X I).PreservesMonomorphisms where
  preserves {F G} f hf := by
    have _ : F.obj.IsCoherent := F.property
    have _ : G.obj.IsCoherent := G.property
    have _ : F.obj.IsQuasicoherent :=
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F.obj).1
    have _ : G.obj.IsQuasicoherent :=
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G.obj).1
    have hmono : Mono (C := X.Modules) f.hom := mono_hom_of_mono f hf
    rw [Preadditive.mono_iff_cancel_zero]
    intro S γ hγ
    have key : ∀ n : ℕ, γ.hom.app (op n) = 0 := by
      intro n
      refine hom_eq_zero_of_affineOpens_app _ fun U a => ?_
      obtain ⟨c, hc⟩ := exists_artinRees_affine I f.hom hmono U
      have hnm : n ≤ n + c := Nat.le_add_right n c
      have _ : (S.obj.obj (op n)).IsQuasicoherent := S.property.isQuasicoherent n
      have _ : (S.obj.obj (op (n + c))).IsQuasicoherent := S.property.isQuasicoherent (n + c)
      have _ : Epi (S.obj.map (homOfLE hnm).op) := S.property.epi_map hnm
      obtain ⟨b, hb⟩ := AlgebraicGeometry.surjective_app_of_epi_of_isAffineOpen
        (S.obj.map (homOfLE hnm).op) U.2 a
      set T := ((completionFunctor X I).obj F).obj.map (homOfLE hnm).op with hT
      set y := Scheme.Modules.Hom.app (γ.hom.app (op (n + c))) U.1 b with hy
      obtain ⟨s, hs0⟩ := completionProjection_app_surjective X I F (n + c) U y
      have hs : Scheme.Modules.Hom.app (completionProjection X I F (n + c)) U.1 s = y :=
        (app_eq_val_app _ _ _).trans hs0
      -- the image of `s` in `G` dies at level `n + c`
      have hγc : γ.hom.app (op (n + c)) ≫
          ((completionFunctor X I).map f).hom.app (op (n + c)) = 0 :=
        congrArg (fun k : S ⟶ (completionFunctor X I).obj G => k.hom.app (op (n + c))) hγ
      have hyzero : Scheme.Modules.Hom.app
          (((completionFunctor X I).map f).hom.app (op (n + c))) U.1 y = 0 := by
        have h0 := congrArg (fun k => Scheme.Modules.Hom.app k U.1 b) hγc
        simpa [hy] using h0
      have hfs : Scheme.Modules.Hom.app (completionProjection X I G (n + c)) U.1
          (Scheme.Modules.Hom.app f.hom U.1 s) = 0 := by
        have h1 : Scheme.Modules.Hom.app
              (((completionFunctor X I).map f).hom.app (op (n + c))) U.1
              (Scheme.Modules.Hom.app (completionProjection X I F (n + c)) U.1 s) =
            Scheme.Modules.Hom.app (completionProjection X I G (n + c)) U.1
              (Scheme.Modules.Hom.app f.hom U.1 s) :=
          (app_comp_apply _ _ _ _).symm.trans
            ((congrArg (fun k => Scheme.Modules.Hom.app k U.1 s)
              (completionFunctor_map_quotient X I f (n + c))).trans
              (app_comp_apply _ _ _ _))
        rw [hs] at h1
        exact h1.symm.trans hyzero
      -- Artin–Rees pushes `s` into the kernel of the projection at level `n`
      have hmemG : Scheme.Modules.Hom.app f.hom U.1 s ∈
          (idealPowerMultiple I ((n + 1) + c) G.obj).toSubmodule.obj (op U.1) := by
        rw [show n + 1 + c = n + c + 1 by lia]
        exact (completionProjection_app_eq_zero_iff X I G (n + c) U _).mp hfs
      -- conclude
      calc Scheme.Modules.Hom.app (γ.hom.app (op n)) U.1 a
          = Scheme.Modules.Hom.app (γ.hom.app (op n)) U.1
              (Scheme.Modules.Hom.app (S.obj.map (homOfLE hnm).op) U.1 b) := by rw [hb]
        _ = Scheme.Modules.Hom.app
              (S.obj.map (homOfLE hnm).op ≫ γ.hom.app (op n)) U.1 b :=
            (app_comp_apply _ _ _ _).symm
        _ = Scheme.Modules.Hom.app (γ.hom.app (op (n + c)) ≫ T) U.1 b :=
            congrArg (fun k => Scheme.Modules.Hom.app k U.1 b)
              (γ.hom.naturality (homOfLE hnm).op)
        _ = Scheme.Modules.Hom.app T U.1 y := app_comp_apply _ _ _ _
        _ = Scheme.Modules.Hom.app T U.1
              (Scheme.Modules.Hom.app (completionProjection X I F (n + c)) U.1 s) := by rw [hs]
        _ = Scheme.Modules.Hom.app (completionProjection X I F (n + c) ≫ T) U.1 s :=
            (app_comp_apply _ _ _ _).symm
        _ = Scheme.Modules.Hom.app (completionProjection X I F n) U.1 s :=
            congrArg (fun k => Scheme.Modules.Hom.app k U.1 s)
              (completionProjection_map X I F (m := op (n + c)) (n := op n) (homOfLE hnm).op)
        _ = 0 := (completionProjection_app_eq_zero_iff X I F n U s).mpr (hc (n + 1) s hmemG)
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun k => ?_))
    obtain ⟨n⟩ := k
    simpa using key n

/-- **Stacks 0881: the completion functor `Coh(𝒪_X) ⥤ Coh(X, I)` of Stacks 0880 is exact.**

It is right exact because the completion of a coherent module is a quotient construction, and it
preserves monomorphisms by Artin–Rees; a right exact functor between abelian categories which
preserves monomorphisms is exact. -/
@[stacks 0881]
public theorem completionFunctor_exact :
    exactFunctor _ _ (completionFunctor X I) := by
  rw [exactFunctor_iff]
  have hcolim : PreservesFiniteColimits (completionFunctor X I) :=
    completionFunctor_preservesFiniteColimits X I
  have _ := hcolim
  exact ⟨Stacks.Coherent.preservesFiniteLimits_of_preservesMonos_of_rightExact _, hcolim⟩

end LeftExact

end Stacks.Algebraization

end
