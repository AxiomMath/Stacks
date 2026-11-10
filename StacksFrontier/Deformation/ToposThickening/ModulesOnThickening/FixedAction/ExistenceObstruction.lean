module

public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction.Torsor
import all StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction.Torsor

/-!
# Extensions with a fixed first-order action: the existence obstruction

Fix a first order thickening `i` of ringed topoi with square-zero ideal `I`. This file builds
the class in `Ext²_{i_*O'}(F, K)` obstructing the existence of an extension of `F` by `K` over
the thickening inducing a prescribed action `c` of `I`
(`Deformation.ToposThickening.existenceObstructionClass`, **Stacks 08MF**), and proves its
vanishing criterion (`Deformation.ToposThickening.existenceObstructionClass_eq_zero_iff`).

See `StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction` for an overview.

## References

* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}}
  {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]

/-! ### Naturality of the action map in the kernel module -/

omit [HasSheafify Y.J AddCommGrpCat.{w'}] in
/-- The map on the tensor products with the square-zero ideal induced by the identity is the
identity. -/
private lemma idealTensorHom_id (hi : FirstOrderThickening i)
    (F : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
        i.toToposHom).obj X.O))) :
    idealTensorHom hi (𝟙 F) = 𝟙 _ := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
    i.toToposHom).obj X.O)
  have hval : (SheafOfModules.forget R).map (𝟙 F) = 𝟙 F.val :=
    CategoryTheory.Functor.map_id (SheafOfModules.forget R) F
  have h : PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 hi.I.val)
        ((SheafOfModules.forget R).map (𝟙 F)) =
      𝟙 (PresheafOfModulesOfCommRing.Monoidal.tensorObj hi.I.val F.val) := by
    rw [hval]
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a x
    rfl
  change (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 hi.I.val)
      ((SheafOfModules.forget R).map (𝟙 F))) = 𝟙 _
  rw [h]
  exact CategoryTheory.Functor.map_id _ _

/-- A map of middle terms over the identity on the quotient module and a map `k` of kernel
modules intertwines the two action maps: the action of the source extension followed by `k` is
the action of the target extension. -/
private lemma extensionActionMap_naturality (hi : FirstOrderThickening i)
    {F K L : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (E' : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj L) 0)
    (k : K ⟶ L) (u : E.Z.left ⟶ E'.Z.left)
    (hf : E.f ≫ u = (SheafOfModules.restrictScalars
      (structureRingMap i)).map k ≫ E'.f)
    (hg : u ≫ E'.g = E.g) :
    (extensionActionMap hi E).1 ≫ k = (extensionActionMap hi E').1 := by
  let D : TwoExtensions i :=
    { thickening := hi, F := F, K := K, G := F, L := L
      firstExtension := E, secondExtension := E'
      quotientMap := 𝟙 F, kernelMap := k }
  have hq : u ≫ E'.g = E.g ≫ (SheafOfModules.restrictScalars
      (structureRingMap i)).map (𝟙 F) := by
    rwa [CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := idealActionMap_naturality D u hf hq
  change (extensionActionMap hi E).1 ≫ k =
    idealTensorHom hi (𝟙 F) ≫ (extensionActionMap hi E').1 at hn
  rwa [idealTensorHom_id, Category.id_comp] at hn

section ExistenceObstruction

/-! The two spellings of the scalars — the commutative ring `O.obj.obj U` of sections of `O` and
the ring `(Tensor.ringSheaf O).obj.obj U` of sections of the sheaf of rings underlying it, which
differ by `forget₂ CommRingCat RingCat` — are definitionally but not reducibly equal, so a module
over one is not found by instance search at the other. The transport both ways is supplied
centrally by the provider of `Tensor.ringSheaf`:
`Stacks.SheafOfModules.Tensor.ringSheafSectionCommRing`,
`Stacks.SheafOfModules.Tensor.ringSheafSectionModule` and
`Stacks.SheafOfModules.Tensor.ringSheafSectionModuleOfCommRing`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget`);
this section adds no bridging instance of its own, and in particular leaves `Tensor.ringSheaf`
opaque, which is what keeps the two categories `SheafOfModules` indexes by the two spellings from
being conflated.

The attribute block lists the definitions along the way between the two spellings, so that the
`change`s below see through them. It stops short of `Tensor.ringSheaf`, and that asymmetry has a
consequence worth recording: a term whose *declared* type names `Tensor.ringSheaf` while its body
names `sheafCompose` — `structureRingMap`, and the ascription inside the type of
`Deformation.ToposThickening.FirstOrderThickening.incl` — is not type-correct at `implicit`
transparency, so `rw` cannot match a pattern whose scalars sit at the other spelling. Where that
bites, the lemma is applied as a term with the scalar given explicitly, which elaborates at
default transparency, instead of being matched by `rw`. -/

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

/-! ### Multiplication by the square-zero ideal on a module over the thickening -/

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- A section of the square-zero ideal annihilates every module restricted from the quotient
structure sheaf. -/
private lemma ideal_annihilates_restrictScalars (hi : FirstOrderThickening i)
    (M : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U)
    (x : ((SheafOfModules.restrictScalars
      (structureRingMap i)).obj M).val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
      from hi.incl.val.app U a) • x = 0 := by
  have ha := (hi.kernel U (hi.incl.val.app U a)).2 ⟨a, rfl⟩
  change (i.fSharp.hom.app U (hi.incl.val.app U a)) • (show M.val.obj U from x) = 0
  rw [ha, zero_smul]

/-- Multiplication by the square-zero ideal on a module `H` over the thickened structure sheaf:
the map `I ⊗_O H ⟶ H` carrying a pure tensor to the product of its factors. -/
private noncomputable def idealMultiplication (hi : FirstOrderThickening i)
    (H : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    { l : ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj H).obj
        ((SheafOfModules.restrictScalars
          (structureRingMap i)).obj hi.I) ⟶ H //
      ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : H.val.obj U),
        l.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)).unit.app
          (PresheafOfModules.tensorObj (((SheafOfModules.restrictScalars
              (structureRingMap i)).obj hi.I)).val H.val)).app U (a ⊗ₜ[Y.O.obj.obj U] x)) =
          (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
            from hi.incl.val.app U a) • x } := by
  apply tensorSheafLift Y.O
    (fun U =>
      -- The multiplication is built with every scalar at the `Tensor.ringSheaf` spelling, where
      -- `LinearMap.comp` finds its `RingHomCompTriple`; the ascription below is what hands it to
      -- `tensorSheafLift`, whose pairings are indexed by the commutative sections.
      let multiplyBySection :
          ((SheafOfModules.restrictScalars (structureRingMap i)).obj hi.I).val.obj U →ₗ[
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U]
            (H.val.obj U →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U]
              H.val.obj U) :=
        (LinearMap.lsmul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
          (H.val.obj U)).comp (hi.incl.val.app U).hom
      multiplyBySection)
  intro U V f a x
  change (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V
      from hi.incl.val.app V (hi.I.val.map f a)) • H.val.map f x =
    H.val.map f ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
      from hi.incl.val.app U a) • x)
  have he := PresheafOfModules.naturality_apply hi.incl.val f a
  change hi.incl.val.app V (hi.I.val.map f a) = Y.O.obj.map f (hi.incl.val.app U a) at he
  rw [H.val.map_smul, he]
  rfl

omit [HasSheafify Y.J AddCommGrpCat.{w'}] in
/-- Multiplication by the square-zero ideal is the inclusion of the ideal tensored with `H`,
followed by the identification of `O ⊗_O H` with `H`. -/
private lemma idealMultiplication_eq_tensor_inclusion (hi : FirstOrderThickening i)
    (H : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (idealMultiplication hi H).1 =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj H).map hi.incl ≫
        (tensorSheafUnitIso Y.O H).hom := by
  apply tensorSheaf_hom_ext Y.O
  intro U a x
  change (idealMultiplication hi H).1.val.app U _ =
    (tensorSheafUnitIso Y.O H).hom.val.app U
      ((((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj H).map hi.incl).val.app U _)
  rw [(idealMultiplication hi H).2, tensorSheaf_map_unit_tmul]
  exact (tensorSheafUnitIso_hom_unit_tmul Y.O H U (hi.incl.val.app U a) x).symm

omit [HasSheafify Y.J AddCommGrpCat.{w'}] in
/-- For a flat module `H` over the thickened structure sheaf, multiplication by the square-zero
ideal is injective: the ideal tensored with `H` is the submodule `I·H`. -/
private lemma idealMultiplication_mono (hi : FirstOrderThickening i)
    (H : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hH : AlgebraicGeometry.SheafOfModules.IsFlat H) :
    Mono (idealMultiplication hi H).1 := by
  have : Mono hi.incl := ⟨fun {Z} f g h => by
    ext U x
    apply hi.injective U
    exact congrArg (fun φ => φ.val.app U x) h⟩
  have : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj H) := hH.1
  rw [idealMultiplication_eq_tensor_inclusion]
  infer_instance

omit [HasSheafify Y.J AddCommGrpCat.{w'}] in
/-- Multiplication by the square-zero ideal dies on any map to a module restricted from the
quotient structure sheaf. -/
private lemma idealMultiplication_comp_eq_zero (hi : FirstOrderThickening i)
    {H : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {F : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (p : H ⟶ (SheafOfModules.restrictScalars
      (structureRingMap i)).obj F) :
    (idealMultiplication hi H).1 ≫ p = 0 := by
  apply tensorSheaf_hom_ext Y.O
  intro U a x
  change p.val.app U ((idealMultiplication hi H).1.val.app U _) = 0
  rw [(idealMultiplication hi H).2 U a x]
  exact ((p.val.app U).hom.map_smul _ x).trans
    (ideal_annihilates_restrictScalars hi F U a (p.val.app U x))

/-- If multiplication by the square-zero ideal on `H` dies on an epimorphism `H ⟶ M`, then the
ideal annihilates `M`, section by section. -/
private lemma ideal_annihilates_of_epi (hi : FirstOrderThickening i)
    {H M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (q : H ⟶ M) [Epi q] (hq : (idealMultiplication hi H).1 ≫ q = 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : M.val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
      from hi.incl.val.app U a) • x = 0 := by
  have : Presheaf.IsLocallySurjective Y.J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj).map q.val) :=
    sheafModule_epi_locallySurjective q
  refine smul_eq_zero_of_locallySurjective q U _ x ?_
  intro V t y
  have ha := PresheafOfModules.naturality_apply hi.incl.val t.op a
  change hi.incl.val.app _ (hi.I.val.map t.op a) =
    Y.O.obj.map t.op (hi.incl.val.app U a) at ha
  have h := congrArg (fun g => g.val.app (Opposite.op V)
    (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)).unit.app
      (PresheafOfModules.tensorObj (((SheafOfModules.restrictScalars
        (structureRingMap i)).obj hi.I)).val H.val)).app _
          (hi.I.val.map t.op a ⊗ₜ[Y.O.obj.obj _] y))) hq
  change q.val.app _ ((idealMultiplication hi H).1.val.app _ _) = 0 at h
  rw [(idealMultiplication hi H).2] at h
  change Y.O.obj.map t.op (hi.incl.val.app U a) • q.val.app (Opposite.op V) y = 0
  rw [← ha]
  exact ((q.val.app (Opposite.op V)).hom.map_smul
    (hi.incl.val.app (Opposite.op V) (hi.I.val.map t.op a)) y).symm.trans h

/-- The quotient of a module over the thickened structure sheaf by the image of multiplication by
the square-zero ideal descends along the structure map. -/
private lemma exists_idealQuotient (hi : FirstOrderThickening i)
    (H : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ∃ (Q : SheafOfModules.{w'}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
          i.toToposHom).obj X.O)))
      (q : H ⟶ (SheafOfModules.restrictScalars
        (structureRingMap i)).obj Q)
      (w : (idealMultiplication hi H).1 ≫ q = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ q w)) := by
  let μ := (idealMultiplication hi H).1
  have hc : (SheafOfModules.restrictScalars
      (structureRingMap i)).essImage
        (cokernel μ) := by
    apply (hi.essImage_restrictScalars_iff (cokernel μ)).2
    intro U a x
    exact ideal_annihilates_of_epi hi (cokernel.π μ) (cokernel.condition μ) U a x
  obtain ⟨Q, ⟨e⟩⟩ := hc
  refine ⟨Q, cokernel.π μ ≫ e.inv,
    by rw [← Category.assoc, cokernel.condition, zero_comp], ⟨?_⟩⟩
  apply CokernelCofork.IsColimit.ofπ'
  intro T k hk
  refine ⟨e.hom ≫ cokernel.desc μ k hk, ?_⟩
  rw [Category.assoc, Iso.inv_hom_id_assoc, cokernel.π_desc]

omit [HasSheafify Y.J AddCommGrpCat.{w'}] in
/-- Multiplication by the square-zero ideal is natural in the module: a map of modules over the
thickened structure sheaf intertwines the two multiplications. -/
private lemma idealMultiplication_naturality (hi : FirstOrderThickening i)
    {N H : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (j : N ⟶ H) :
    tensorSheafMapRight Y.O ((SheafOfModules.restrictScalars
          (structureRingMap i)).obj hi.I) j ≫
        (idealMultiplication hi H).1 =
      (idealMultiplication hi N).1 ≫ j := by
  apply tensorSheaf_hom_ext Y.O
  intro U a x
  change (idealMultiplication hi H).1.val.app U
      ((tensorSheafMapRight Y.O _ j).val.app U _) =
    j.val.app U ((idealMultiplication hi N).1.val.app U _)
  rw [tensorSheafMapRight_unit_tmul, (idealMultiplication hi H).2,
    (idealMultiplication hi N).2]
  exact ((j.val.app U).hom.map_smul _ x).symm

/-! ### An extension whose action map is injective -/

/-- An extension built from a flat presentation of `F` has injective action map: the ideal
multiplication on the flat cover is injective and factors through the kernel of the
presentation, whose ideal quotient is the kernel module of the extension. -/
private lemma extensionActionMap_mono_of_flat_presentation (hi : FirstOrderThickening i)
    {F Q : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj Q) 0)
    {N H : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (j : N ⟶ H)
    (p : H ⟶ (SheafOfModules.restrictScalars
      (structureRingMap i)).obj F)
    (w : j ≫ p = 0) (hS : (ShortComplex.mk j p w).ShortExact)
    (hH : AlgebraicGeometry.SheafOfModules.IsFlat H)
    (q : N ⟶ (SheafOfModules.restrictScalars
      (structureRingMap i)).obj Q)
    (wq : (idealMultiplication hi N).1 ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q wq))
    (u : H ⟶ E.Z.left) (hu : j ≫ u = q ≫ E.f) (hp : u ≫ E.g = p) :
    Mono (extensionActionMap hi E).1 := by
  let α := structureRingMap i
  let R := SheafOfModules.restrictScalars α
  let T := (pushforwardCommRingFunctor i.toToposHom).obj X.O
  let t := tensorSheafMapRight Y.O (R.obj hi.I) j
  let b := tensorSheafRestrictMap Y.O T α hi.I F p
  have : Mono j := hS.mono_f
  have : Epi p := hS.epi_g
  let l := hS.exact.lift (idealMultiplication hi H).1 (idealMultiplication_comp_eq_zero hi p)
  have hl : l ≫ j = (idealMultiplication hi H).1 := hS.exact.lift_f _ _
  have : Mono (idealMultiplication hi H).1 := idealMultiplication_mono hi H hH
  have : Mono l := mono_of_mono_fac hl
  have ht : t ≫ l = (idealMultiplication hi N).1 := by
    apply (cancel_mono j).1
    rw [Category.assoc, hl]
    exact idealMultiplication_naturality hi j
  have hb : t ≫ b.1 = 0 := by
    apply tensorSheaf_hom_ext Y.O
    intro U a x
    change b.1.val.app U (t.val.app U _) = 0
    rw [tensorSheafMapRight_unit_tmul, b.2]
    have hw := congrArg (fun f => f.val.app U x) w
    change p.val.app U (j.val.app U x) = 0 at hw
    rw [hw, TensorProduct.tmul_zero]
    exact map_zero _
  have hd : b.1 ≫ R.map (extensionActionMap hi E).1 = l ≫ q := by
    apply tensorSheaf_hom_ext Y.O
    intro U a x
    have : Mono E.f.val := (SheafOfModules.forget _).map_mono E.f
    apply PresheafOfModules.injective_of_mono E.f.val U
    have hl' := congrArg (fun f => f.val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)).unit.app
        (PresheafOfModules.tensorObj ((R.obj hi.I)).val H.val)).app U (a ⊗ₜ[Y.O.obj.obj U] x))) hl
    have hu' := congrArg (fun f => f.val.app U
      (l.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)).unit.app
        (PresheafOfModules.tensorObj ((R.obj hi.I)).val H.val)).app U
        (a ⊗ₜ[Y.O.obj.obj U] x)))) hu
    have hp' := congrArg (fun f => f.val.app U x) hp
    change E.g.val.app U (u.val.app U x) = p.val.app U x at hp'
    change j.val.app U (l.val.app U _) = (idealMultiplication hi H).1.val.app U _ at hl'
    change u.val.app U (j.val.app U _) = E.f.val.app U (q.val.app U _) at hu'
    change E.f.val.app U ((extensionActionMap hi E).1.val.app U (b.1.val.app U _)) =
      E.f.val.app U (q.val.app U (l.val.app U _))
    rw [b.2]
    have he := (extensionActionMap hi E).2 U a (u.val.app U x)
    rw [hp'] at he
    exact he.trans (((u.val.app U).hom.map_smul _ x).symm.trans
      ((congrArg (u.val.app U) ((hl'.trans ((idealMultiplication hi H).2 U a x)).symm)).trans
        hu'))
  have : Epi b.1 := tensorSheafRestrictMap_epi Y.O T α hi.I F p
  have hq' : IsColimit (CokernelCofork.ofπ (f := t ≫ l) q (by rwa [ht])) := by
    let : Epi q := Cofork.IsColimit.epi hq
    apply CokernelCofork.IsColimit.ofπ'
    intro A k hk
    exact CokernelCofork.IsColimit.desc' hq k (by rwa [← ht])
  have hmono : Mono (R.map (extensionActionMap hi E).1) :=
    Abelian.mono_of_cokernel_diagram t l q (by rw [← Category.assoc, ht]; exact wq) hq' b.1 hb _ hd
  have : R.Faithful := hi.restrictScalarsFullyFaithful.faithful
  exact R.mono_of_mono_map hmono

/-- **Every module over the quotient structure sheaf carries an extension with injective action
map.** Take a flat cover of its restriction, and push the kernel of the cover out along its
ideal quotient. -/
private lemma exists_extension_with_mono_action (hi : FirstOrderThickening i)
    (F : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
        i.toToposHom).obj X.O))) :
    ∃ (Q : SheafOfModules.{w'}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
          i.toToposHom).obj X.O)))
      (E : Abelian.YonedaExtension
        ((SheafOfModules.restrictScalars
          (structureRingMap i)).obj F)
        ((SheafOfModules.restrictScalars
          (structureRingMap i)).obj Q) 0),
      Mono (extensionActionMap hi E).1 := by
  let R := SheafOfModules.restrictScalars
    (structureRingMap i)
  obtain ⟨H, p, hH, hp⟩ :=
    Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat Y.O (R.obj F)
  have : Epi p := hp
  have hS : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
    { exact := ShortComplex.exact_kernel p }
  obtain ⟨Q, q, wq, ⟨hq⟩⟩ := exists_idealQuotient hi (kernel p)
  obtain ⟨E, u, hu, hg⟩ := Abelian.shortExact_pushout hS q
  exact ⟨Q, E, extensionActionMap_mono_of_flat_presentation hi E (kernel.ι p) p
    (kernel.condition p) hS hH q wq hq u hu hg⟩

/-! ### Descending an extension with vanishing action map -/

/-- An extension with vanishing action map is restricted from an extension of modules over the
quotient structure sheaf: the ideal annihilates its middle term, so that term descends. -/
private lemma zeroAction_extension_descend (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (hE : (extensionActionMap hi E).1 = 0) :
    ∃ (D : Abelian.YonedaExtension F K 0)
      (e : (SheafOfModules.restrictScalars
        (structureRingMap i)).obj D.Z.left ≅
          E.Z.left),
      (SheafOfModules.restrictScalars
          (structureRingMap i)).map D.f ≫ e.hom =
        E.f ∧
      e.hom ≫ E.g = (SheafOfModules.restrictScalars
        (structureRingMap i)).map D.g := by
  let α := structureRingMap i
  have hex := restrictScalars_exact α
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars.{w'} α) := hex.1
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars.{w'} α) := hex.2
  apply Abelian.yonedaExtension_descend (SheafOfModules.restrictScalars α)
    hi.restrictScalarsFullyFaithful E
  exact (hi.essImage_restrictScalars_iff E.Z.left).2
    (middle_smul_eq_zero_of_extensionActionMap_eq_zero hi E hE)

/-! ### The obstruction class -/

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- Pushing an extension out along a map of kernel modules multiplies its `Ext` class by that
map and composes its action map with it. -/
private lemma extensionClass_pushout
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    {F K L : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (E' : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj L) 0)
    (γ : K ⟶ L) (u : E.Z.left ⟶ E'.Z.left)
    (hu : E.f ≫ u = (SheafOfModules.restrictScalars
      (structureRingMap i)).map γ ≫ E'.f)
    (hg : u ≫ E'.g = E.g) :
    (extensionClass F K E).comp
      (Abelian.Ext.mk₀ ((SheafOfModules.restrictScalars
        (structureRingMap i)).map γ))
      (add_zero 1) = extensionClass F L E' := by
  have hnat := (yonedaExtension_shortExact E).extClass_naturality
    (yonedaExtension_shortExact E')
    { τ₁ := (SheafOfModules.restrictScalars
        (structureRingMap i)).map γ
      τ₂ := u, τ₃ := 𝟙 _
      comm₁₂ := hu.symm, comm₂₃ := by simpa using hg }
  simpa only [extensionClass, Abelian.Ext.mk₀_id_comp] using hnat

/-- The action map attached to the `Ext` class of a pushout: composing the class with a map of
kernel modules composes the action map with that map. -/
private lemma actionOfExt_pushout
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    {F K L : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj K) 0)
    (γ : K ⟶ L) :
    actionOfExt hi F L ((extensionClass F K E).comp
        (Abelian.Ext.mk₀ ((SheafOfModules.restrictScalars
          (structureRingMap i)).map γ))
        (add_zero 1)) =
      (extensionActionMap hi E).1 ≫ γ := by
  let R := SheafOfModules.restrictScalars
    (structureRingMap i)
  obtain ⟨E', u, hu, hg⟩ := Abelian.shortExact_pushout (yonedaExtension_shortExact E) (R.map γ)
  rw [extensionClass_pushout E E' γ u hu hg, actionOfExt_extensionClass]
  exact (extensionActionMap_naturality hi E E' γ u hu hg).symm


/-- The obstruction class and its vanishing criterion, computed from any extension of `F` whose
action map is injective: the Yoneda product of the class of the descent of that extension's
pushout along the cokernel of its action map with the class of the pushout of the cokernel
sequence along `c`. -/
private noncomputable def obstructionFromMonoAction
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K)
    {Q : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj F)
      ((SheafOfModules.restrictScalars
        (structureRingMap i)).obj Q) 0)
    (hdm : Mono (extensionActionMap hi E).1) :
    { o : Abelian.Ext F K 2 //
      o = 0 ↔ ∃ E' : Abelian.YonedaExtension
        ((SheafOfModules.restrictScalars
          (structureRingMap i)).obj F)
        ((SheafOfModules.restrictScalars
          (structureRingMap i)).obj K) 0,
        (extensionActionMap hi E').1 = c } := by
  classical
  let α := structureRingMap i
  let R := SheafOfModules.restrictScalars.{w'} α
  have hex := restrictScalars_exact α
  have : PreservesFiniteLimits R := hex.1
  have : PreservesFiniteColimits R := hex.2
  let ff := hi.restrictScalarsFullyFaithful
  have : R.Full := ff.full
  have : R.Faithful := ff.faithful
  let d := (extensionActionMap hi E).1
  let q : Q ⟶ cokernel d := cokernel.π d
  have : Mono d := hdm
  have hS : (ShortComplex.mk d q (cokernel.condition d)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel d) inferInstance inferInstance
  let P := Classical.choose (Abelian.shortExact_pushout hS c)
  let uP := Classical.choose (Classical.choose_spec (Abelian.shortExact_pushout hS c))
  have hPu : d ≫ uP = c ≫ P.f :=
    (Classical.choose_spec (Classical.choose_spec (Abelian.shortExact_pushout hS c))).1
  have hPg : uP ≫ P.g = q :=
    (Classical.choose_spec (Classical.choose_spec (Abelian.shortExact_pushout hS c))).2
  let hpush := Abelian.shortExact_pushout (yonedaExtension_shortExact E) (R.map q)
  let D' := Classical.choose hpush
  let uD := Classical.choose (Classical.choose_spec hpush)
  have hDu : E.f ≫ uD = R.map q ≫ D'.f :=
    (Classical.choose_spec (Classical.choose_spec hpush)).1
  have hDg : uD ≫ D'.g = E.g := (Classical.choose_spec (Classical.choose_spec hpush)).2
  have hD' : (extensionActionMap hi D').1 = 0 := by
    rw [← extensionActionMap_naturality hi E D' q uD hDu hDg]
    exact cokernel.condition d
  let hdesc := zeroAction_extension_descend hi D' hD'
  let D := Classical.choose hdesc
  let mD := Classical.choose (Classical.choose_spec hdesc)
  have hmD₁ : R.map D.f ≫ mD.hom = D'.f :=
    (Classical.choose_spec (Classical.choose_spec hdesc)).1
  have hmD₂ : mD.hom ≫ D'.g = R.map D.g :=
    (Classical.choose_spec (Classical.choose_spec hdesc)).2
  refine ⟨(yonedaExtension_shortExact D).extClass.comp
    (yonedaExtension_shortExact P).extClass (by decide), ?_⟩
  have hDc : R.mapExtAddHom F (cokernel d) 1 (yonedaExtension_shortExact D).extClass =
      extensionClass F (cokernel d) D' :=
    R.mapExtAddHom_extClass_of_yoneda_iso D D' mD hmD₁ hmD₂
  have hxy : ((extensionClass F Q E).comp (Abelian.Ext.mk₀ (R.map uP)) (add_zero 1)).comp
      (Abelian.Ext.mk₀ (R.map P.g)) (add_zero 1) =
      R.mapExtAddHom F (cokernel d) 1 (yonedaExtension_shortExact D).extClass := by
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, ← R.map_comp, hPg]
    exact (extensionClass_pushout E D' q uD hDu hDg).trans hDc.symm
  have ha {L M : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
      (x : Abelian.Ext (R.obj F) (R.obj L) 1) (f : L ⟶ M) :
      actionExtAddHom hi F M (x.comp (Abelian.Ext.mk₀ (R.map f)) (add_zero 1)) =
        actionExtAddHom hi F L x ≫ f := by
    obtain ⟨E', rfl⟩ := exists_extensionClass_eq F L x
    exact (actionOfExt_pushout hi E' f).trans
      (congrArg (· ≫ f) (actionOfExt_extensionClass hi E').symm)
  have hc : actionExtAddHom hi F Q (extensionClass F Q E) ≫ uP = c ≫ P.f := by
    change actionOfExt hi F Q (extensionClass F Q E) ≫ uP = _
    rwa [actionOfExt_extensionClass]
  refine (Abelian.boundary_eq_zero_iff_exists_action R F _ (actionExtAddHom hi F) ha
    (fun L x => actionExtAddHom_eq_zero_iff hi F L x) (yonedaExtension_shortExact P) uP
    (extensionClass F Q E) c hc (yonedaExtension_shortExact D).extClass hxy).trans ?_
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨E', hE'⟩ := exists_extensionClass_eq F K x
    exact ⟨E', by rw [← actionOfExt_extensionClass hi E', hE']; exact hx⟩
  · rintro ⟨E', hE'⟩
    exact ⟨extensionClass F K E', (actionOfExt_extensionClass hi E').trans hE'⟩

/-- **Stacks 08MF.** The obstruction to the existence of an extension over a first order
thickening of ringed topoi inducing a prescribed action `c` of the square-zero ideal: a class in
the second `Ext` group over the quotient structure sheaf. -/
@[no_expose, stacks 08MF "obstruction class"]
noncomputable def existenceObstructionClass
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K) :
    Abelian.Ext F K 2 :=
  (obstructionFromMonoAction hi F K c
    (Classical.choose (Classical.choose_spec (exists_extension_with_mono_action hi F)))
    (Classical.choose_spec (Classical.choose_spec
      (exists_extension_with_mono_action hi F)))).1

/-- **Stacks 08MF.** The obstruction class vanishes exactly when there is an extension of `F` by
`K` over the first order thickening whose canonical action of the square-zero ideal is `c`. -/
@[stacks 08MF "vanishing criterion"]
theorem existenceObstructionClass_eq_zero_iff
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K) :
    existenceObstructionClass hi F K c = 0 ↔
      ∃ E : Abelian.YonedaExtension
        ((SheafOfModules.restrictScalars
          (structureRingMap i)).obj F)
        ((SheafOfModules.restrictScalars
          (structureRingMap i)).obj K) 0,
        (extensionActionMap hi E).1 = c :=
  (obstructionFromMonoAction hi F K c
    (Classical.choose (Classical.choose_spec (exists_extension_with_mono_action hi F)))
    (Classical.choose_spec (Classical.choose_spec
      (exists_extension_with_mono_action hi F)))).2

end ExistenceObstruction

end Deformation.ToposThickening

end
