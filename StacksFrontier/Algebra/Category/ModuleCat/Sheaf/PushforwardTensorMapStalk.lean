module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackAssociativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorMixed
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkBaseChangeMate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DirectImageFiberMapGerm
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence
public import StacksFrontier.CategoryTheory.Sites.Point.DirectImageFiber
public import StacksFrontier.LinearAlgebra.TensorProduct.BaseChangeCancellation
public import StacksFrontier.LinearAlgebra.TensorProduct.BaseChangePi

/-!
# The canonical map `G ⊗ f_*F ⟶ f_*(f^*G ⊗ F)` on stalks

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi, `G` a sheaf of
`𝒪'`-modules and `F` a sheaf of `𝒪`-modules, and let

`τ : G ⊗_{𝒪'} f_*F ⟶ f_*(f^*G ⊗_𝒪 F)`

be the canonical map, the adjoint transpose of the comparison of Stacks 03EL followed by the
counit (`Stacks.SheafOfModules.pushforwardTensorMap`). This file computes the stalk of `τ` at a
point `Ψ` of `D` in terms of the stalks at points `Φ` of `C` identified with `Ψ` along `f`, and
deduces the criterion through which the projection formula for a finite morphism of algebraic
spaces (Stacks 0DK4) is proved: if the stalk at `Ψ` of every direct image of a sheaf of sets is
the product of its stalks at finitely many such points `Φ i`, then the stalk of `τ` at `Ψ` is an
isomorphism; hence `τ` is an isomorphism as soon as this holds at a conservative family of
points.

The computation is the one the source makes. Writing `G_Ψ`, `F_{Φ i}` for the stalks, the stalk
of `f_*F` at `Ψ` is `∏ᵢ F_{Φ i}`, the stalk of `f^*G` at `Φ i` is `𝒪_{Φ i} ⊗_{𝒪'_Ψ} G_Ψ`
(Stacks 05V5), stalks commute with tensor products, and on germs of pure tensors the stalk of `τ`
is `g ⊗ (sᵢ)ᵢ ↦ ((1 ⊗ g) ⊗ sᵢ)ᵢ`, which is the isomorphism
`TensorProduct.tensorPiBaseChangeEquiv`.

## Main definitions

* `Stacks.SheafOfModules.pushforwardStalkHom`: the map `(f_*N)_Ψ ⟶ N_Φ` of stalks of modules,
  Stacks 05V1 at the direct image followed by the stalk of the counit of Stacks 03D3.
* `Stacks.SheafOfModules.pullbackStalkHom`: the map `G_Ψ ⟶ (f^*G)_Φ` of stalks of modules.
* `Stacks.SheafOfModules.pushforwardStalkPiHom`: the maps `(f_*N)_Ψ ⟶ N_{Φ i}` assembled into a
  semilinear map to the product.
* `Stacks.SheafOfModules.stalkBaseChangeEquiv`: Stacks 05V5 at `(Φ i, Ψ)` as a base change,
  `(f^*G)_{Φ i} = 𝒪_{Φ i} ⊗_{𝒪'_Ψ} G_Ψ`.

## Main results

* `Stacks.SheafOfModules.pushforwardTensorMap_app_unit_tmul`: on a local pure tensor, `τ` is
  the transpose of the pairing of `f⁻¹G` and `f⁻¹f_*F` produced by steps 4 to 6 of the chain of
  Stacks 03EL.
* `tensorSheafModuleFiberIso_hom_pushforwardStalkHom_map_pushforwardTensorMap` (in the
  namespace `Stacks.SheafOfModules`) computes the stalk of `τ` on the germ of a local pure tensor.
* `Stacks.SheafOfModules.pushforwardStalkHom_smul`: the map of stalks of a direct image is
  semilinear over the map `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings of Stacks 05V5.
* `Stacks.SheafOfModules.isIso_sheafModuleFiberOfCommRing_map_pushforwardTensorMap`: the stalk
  of `τ` at `Ψ` is an isomorphism when the stalk at `Ψ` of a direct image of sheaves of sets is the
  product of its stalks at finitely many points identified with `Ψ`.
* `Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isConservativeFamilyOfPoints`: `τ` is an
  isomorphism when this holds at a conservative family of points of `D`.

## Implementation notes

The identifications `e i : Ψ⁻¹ ≅ f⁻¹ ⋙ (Φ i)⁻¹` of stalk functors on sheaves of sets are data:
they are what Stacks 05V1 and Stacks 05V5 are stated over in this library, and the product
condition is stated for the canonical maps `MorphismOfTopoi.pushforwardFiberMap` they determine,
so it is a condition on the morphism of topoi and the points, not on the module categories. All
the module-theoretic content is proved here.

The computation on germs goes through the chain of bijections of Stacks 03EL, which is how the
comparison `f^*(G ⊗ f_*F) ≅ f^*G ⊗ f^*f_*F` is built (`Stacks.SheafOfModules.pullbackTensorIso`):
the transpose of `τ` across `f⁻¹ ⊣ f_*` is the pairing
`Stacks.SheafOfModules.RingedToposPullback.invChainPairing`, whose value on a pair of local
sections is computed by
`Stacks.SheafOfModules.RingedToposPullback.pairingApp_invChainPairing`.

## References

* [Stacks Project, Tag 0DK4](https://stacks.math.columbia.edu/tag/0DK4)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sheaves.RingedToposModules
  Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback Stacks.Sheaves.StalkTransport
  Stacks.Sheaves.StalkInverseImage
open scoped TensorProduct ChangeOfRings

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` of the cohomology of modules
leaves a stuck universe constraint against the modules here; the abelian structure used is the
one at the pinned universes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe w v u v' u' t

namespace Stacks.SheafOfModules

section Counit

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f : RingedToposHom X Y)

/-- On underlying sheaves of sets, the counit of the adjunction of Stacks 03D3 is the counit of
the adjunction of the underlying topoi. -/
lemma moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit
    (M : SheafOfModules.{w}
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
      ((inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).counit.app M) =
      f.toToposHom.adj.counit.app
        (Sheaf.moduleSheaf
            (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) M) := by
  have h₁ : (inverseImageAdjDirectImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).counit.app
      M = ((inverseImageAdjDirectImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).homEquiv _ _).symm
        (𝟙 _) := by
    rw [Adjunction.homEquiv_counit]
    simp
  have h₂ : ((inverseImageAdjDirectImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).homEquiv
      ((directImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) M).symm (𝟙 _) =
      (toposModulesHomEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _
          M).symm (𝟙 _) := by
    rw [Equiv.symm_apply_eq, inverseImageAdjDirectImageModules_homEquiv_eq,
      Equiv.apply_symm_apply]
  refine (congrArg _ (h₁.trans h₂)).trans ?_
  refine (moduleSheafFunctor_map_toposModulesHomEquiv_symm f.toToposHom _ _).trans ?_
  refine (congrArg (f.toToposHom.adj.homEquiv _ _).symm
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_id _)).trans ?_
  exact (Adjunction.homEquiv_counit _ _ _ _).trans
    ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _))

/-- Composing the unit of extension of scalars along the inverse-image form of the structure
map with the restriction of the counit of `f^* ⊣ f_*` gives the counit of the adjunction of
Stacks 03D3. -/
lemma unit_comp_map_comp_counit {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (M : E) :
    adj₂.unit.app (L₁.obj (R₁.obj (R₂.obj M))) ≫ R₂.map ((adj₁.comp adj₂).counit.app M) =
      adj₁.counit.app (R₂.obj M) := by
  simp [Adjunction.comp_counit_app]

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **On underlying sheaves of sets, the counit of `f^* ⊣ f_*` restricted to the inverse image
is the counit of the adjunction of the underlying topoi**: the unit `f⁻¹G ⟶ O_C ⊗ f⁻¹G` of
extension of scalars followed by the counit `f^*f_*M ⟶ M` is `f⁻¹f_*M ⟶ M`. -/
lemma moduleSheafFunctor_map_unit_comp_counit (M : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
      ((fSharpAdjunction f).unit.app ((inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj ((pushforwardModules f).obj M))) ≫
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
      ((pullbackAdjPushforwardModules f).counit.app M) =
    f.toToposHom.adj.counit.app (Sheaf.moduleSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) := by
  have h₃ : (fSharpAdjunction f).unit.app ((inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj ((pushforwardModules f).obj M)) ≫
      (SheafOfModules.restrictScalars f.fSharpInverseImage).map
        ((pullbackAdjPushforwardModules f).counit.app M) =
      (inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).counit.app
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M) :=
    unit_comp_map_comp_counit (inverseImageAdjDirectImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (fSharpAdjunction f) M
  exact (((Sheaf.moduleSheafFunctor
      (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map_comp _ _).symm.trans
    (congrArg (Sheaf.moduleSheafFunctor
      (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map h₃)).trans
    (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit f _)

end Counit

section RestrictScalars

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w})

/-- The stalk of a restriction of scalars along `α : R ⟶ R'` has its scalars acting through the
stalk of `α`. -/
lemma sheafModuleFiber_restrictScalars_smul {R R' : Sheaf J RingCat.{w}} (α : R ⟶ R')
    (M : SheafOfModules.{w} R') (s : (Φ.presheafFiber (A := RingCat.{w})).obj R.obj)
    (m : (Stacks.sheafModuleFiber Φ R).obj ((SheafOfModules.restrictScalars α).obj M)) :
    s • m = ((Φ.presheafFiber (A := RingCat.{w})).map α.hom s •
      (show (Stacks.sheafModuleFiber Φ R').obj M from m) :
        (Stacks.sheafModuleFiber Φ R').obj M) := by
  obtain ⟨U, x, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := R.obj) s
  obtain ⟨V, y, n, rfl⟩ := Stacks.toPresheafModuleFiber_jointly_surjective Φ
    ((SheafOfModules.restrictScalars α).obj M).val m
  obtain ⟨W, z, i, j, hi, hj⟩ := Stacks.exists_common_nbhd (Φ := Φ) x y
  subst hi hj
  rw [← Φ.toPresheafFiber_w_apply, Stacks.toPresheafModuleFiber_w]
  refine (Stacks.toPresheafModuleFiber_smul Φ _ W z _ _).symm.trans ?_
  refine (Stacks.toPresheafModuleFiber_smul Φ M.val W z _ _).trans ?_
  exact congrArg (fun r => r • (Stacks.toPresheafModuleFiber Φ M.val W z
      (((SheafOfModules.restrictScalars α).obj M).val.map j.op n)))
    (Φ.toPresheafFiber_naturality_apply α.hom W z _).symm

/-- The scalar action on a stalk read over the `CommRingCat`-valued stalk ring is the action of
the `RingCat`-valued stalk ring through `Stacks.toRingFiber`. -/
lemma sheafModuleFiberOfCommRing_smul [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (O : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O))
    (r : Stacks.ringFiber Φ O.obj) (z : (Stacks.sheafModuleFiberOfCommRing Φ O).obj M) :
    r • z = (show (Stacks.sheafModuleFiberOfCommRing Φ O).obj M from
      ((show (Φ.presheafFiber (A := RingCat.{w})).obj (Stacks.commRingSheafToRingSheaf O).obj from
          Stacks.toRingFiber Φ O.obj r) •
        (show (Stacks.sheafModuleFiber Φ (Stacks.commRingSheafToRingSheaf O)).obj M from z))) :=
  rfl

end RestrictScalars

section Point

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) (Ψ : Y.J.Point.{w})
  (e : Ψ.sheafFiber (A := Type w) ≅ f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w))

/-- **The canonical map from the stalk of a direct image of modules to the stalk of the
module**: Stacks 05V1 at the direct image, followed by the stalk of the counit of the
adjunction of Stacks 03D3. -/
def pushforwardStalkHom (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Stacks.sheafModuleFiber Ψ
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj ((pushforwardModules f).obj N) →+
      (Stacks.sheafModuleFiber Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N :=
  ((Stacks.sheafModuleFiber Φ
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
      ((inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).counit.app
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N))).hom.toAddMonoidHom.comp
    (stalkAddEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e
      ((pushforwardModules f).obj N)).toAddMonoidHom

/-- On underlying stalks of sheaves of sets the canonical map is
`MorphismOfTopoi.pushforwardFiberMap`. -/
lemma pushforwardStalkHom_moduleStalkComparison (N : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (x : (Ψ.sheafFiber (A := Type w)).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((pushforwardModules f).obj N))) :
    pushforwardStalkHom f Φ Ψ e N (moduleStalkComparison Ψ
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _ x) =
      moduleStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N
        ((f.toToposHom.pushforwardFiberMap Φ Ψ e).app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) x) := by
  have h := stalkModuleMap_moduleStalkComparison f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e
    ((pushforwardModules f).obj N) x
  change (Stacks.sheafModuleFiber Φ
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
      _ (stalkModuleMap f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e
        ((pushforwardModules f).obj N) _) = _
  rw [h]
  refine (moduleStalkComparison_naturality Φ
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((inverseImageAdjDirectImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).counit.app
      ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)) _).symm.trans ?_
  exact congrArg (fun φ => moduleStalkComparison Φ
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)
      ((Φ.sheafFiber (A := Type w)).map φ (e.hom.app _ x)))
    (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit f _)

omit [LocallySmall.{w} Y.C] [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The comparison of stalks of the underlying sheaves of sets of sheaves of rings is natural. -/
lemma ringStalkComparison_naturality {R R' : Sheaf X.J RingCat.{w}} (α : R ⟶ R')
    (y : (Φ.sheafFiber (A := Type w)).obj (Sheaf.ringSheaf R)) :
    Stacks.Sheaves.StalkTransport.ringStalkComparison Φ R' ((Φ.sheafFiber (A := Type w)).map
        ((sheafCompose X.J (forget RingCat.{w})).map α) y) =
      (Φ.presheafFiber (A := RingCat.{w})).map α.hom
        (Stacks.Sheaves.StalkTransport.ringStalkComparison Φ R y) :=
  ConcreteCategory.congr_hom ((Φ.presheafFiberCompIso (forget RingCat.{w})).hom.naturality
    α.hom) y

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The ring map along which the canonical map of stalks of a direct image is semilinear, read
on the `RingCat`-valued stalks. -/
lemma toRingFiber_stalkRingMap (r : Stacks.ringFiber Ψ Y.O.obj) :
    Stacks.toRingFiber Φ X.O.obj (Stacks.Sheaves.StalkPullback.stalkRingMap f Φ Ψ e r) =
      (Φ.presheafFiber (A := RingCat.{w})).map f.fSharpInverseImage.hom
        (stalkRingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e
          (Stacks.toRingFiber Ψ Y.O.obj r)) := by
  obtain ⟨V, v, t, rfl⟩ := Stacks.ringGerm_jointly_surjective (Φ := Ψ) (O := Y.O.obj) r
  have h₁ : Stacks.toRingFiber Ψ Y.O.obj (Stacks.ringGerm Ψ Y.O.obj V v t) =
      Stacks.Sheaves.StalkTransport.ringStalkComparison Ψ
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (Ψ.toPresheafFiber V v
            (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj t) :=
    (Stacks.toRingFiber_germ V v t).trans
      (ringStalkComparison_germ Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V v t).symm
  refine (congrArg (Stacks.toRingFiber Φ X.O.obj)
    (Stacks.Sheaves.StalkPullback.stalkRingMap_toPresheafFiber f Φ Ψ e V v t)).trans ?_
  refine (ConcreteCategory.congr_hom (Stacks.commRingPresheafFiberIso Φ X.O.obj).hom_inv_id
    _).trans ?_
  refine (ringStalkComparison_naturality Φ f.fSharpInverseImage _).trans ?_
  refine congrArg ((Φ.presheafFiber (A := RingCat.{w})).map f.fSharpInverseImage.hom) ?_
  exact (stalkRingMap_ringStalkComparison f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e _).symm.trans
    (congrArg (stalkRingEquiv f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e) h₁.symm)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The canonical map of stalks of a direct image is semilinear** over the map of stalk rings
`𝒪'_Ψ ⟶ 𝒪_Φ` of Stacks 05V5. -/
lemma pushforwardStalkHom_smul (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (r : Stacks.ringFiber Ψ Y.O.obj)
    (z : (Stacks.sheafModuleFiberOfCommRing Ψ Y.O).obj ((pushforwardModules f).obj N)) :
    pushforwardStalkHom f Φ Ψ e N (r • z) =
      (Stacks.Sheaves.StalkPullback.stalkRingMap f Φ Ψ e r •
        (show (Stacks.sheafModuleFiberOfCommRing Φ X.O).obj N from
          pushforwardStalkHom f Φ Ψ e N z) :
        (Stacks.sheafModuleFiberOfCommRing Φ X.O).obj N) := by
  refine (congrArg (pushforwardStalkHom f Φ Ψ e N)
    (sheafModuleFiberOfCommRing_smul Ψ Y.O _ r z)).trans ?_
  refine Eq.trans ?_ (sheafModuleFiberOfCommRing_smul Φ X.O N _ _).symm
  refine Eq.trans ?_ (congrArg (fun s => (show (Stacks.sheafModuleFiber Φ
    (Stacks.commRingSheafToRingSheaf X.O)).obj N from (s • (show (Stacks.sheafModuleFiber Φ
      (Stacks.commRingSheafToRingSheaf X.O)).obj N from pushforwardStalkHom f Φ Ψ e N z))))
    (toRingFiber_stalkRingMap f Φ Ψ e r).symm)
  refine (congrArg ((Stacks.sheafModuleFiber Φ
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
      ((inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).counit.app
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N))).hom
    (stalkAddEquiv_smul f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e _ _ _)).trans ?_
  refine ((ConcreteCategory.hom ((Stacks.sheafModuleFiber Φ
    (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map _)).map_smul _ _).trans ?_
  exact sheafModuleFiber_restrictScalars_smul Φ f.fSharpInverseImage N _ _

/-- **Stacks 05V5 at a matched pair of points, on the unit image of a germ**: the inverse of the
comparison `(f^*G)_Φ ≅ G_Ψ ⊗_{𝒪'_Ψ} 𝒪_Φ` carries `1 ⊗ g` to the stalk of the unit of
extension of scalars applied to the image of `g` in the stalk of the inverse image. -/
lemma stalkFunctorIso_inv_app_one_tmul (G : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (g : (Stacks.sheafModuleFiberOfCommRing Ψ Y.O).obj G) :
    (Stacks.Sheaves.StalkPullback.stalkFunctorIso f Φ Ψ e).inv.app G
        ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj,
          Stacks.Sheaves.StalkPullback.stalkRingMap f Φ Ψ e] g) =
      (show (Stacks.sheafModuleFiberOfCommRing Φ X.O).obj ((f.pullbackModules).obj G) from
        (Stacks.sheafModuleFiber Φ (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map ((fSharpAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))
          (stalkAddEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e G g)) := by
  open Stacks.Sheaves.StalkPullback in
  have h₂ := ModuleCat.restrictExtendScalarsCompIso_hom_app_one_tmul
    (toInverseImageStalkRing f Φ) (fSharpStalk f Φ) (commRingStalkEquiv f Φ Ψ e)
    ((inverseImageFunctor f ⋙ inverseImageStalkFunctor f Φ).obj G)
    (stalkAddEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e G g)
  have h₁ := Stacks.Sheaves.StalkPullback.unit_square_app Φ (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((inverseImageFunctor f).obj G)
    (stalkAddEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e G g)
  exact (congrArg ((stalkIsoStepOne f Φ).inv.app G) h₂).trans h₁

end Point

section Pairing

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

open AlgebraicGeometry.SheafOfModules Stacks.SheafOfModules.RingedToposPullback
open scoped CategoryTheory.Prod

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The morphism `f^*G ⊗ f^*f_*F ⟶ f^*G ⊗ F` given by the identity and the counit, through which
the canonical map of Stacks 0DK4 is defined. -/
abbrev tensorCounit :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
        ((f.pullbackModules).obj G, (f.pullbackModules).obj ((pushforwardModules f).obj F)) ⟶
      (Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj ((f.pullbackModules).obj G, F) :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).map
    (𝟙 ((f.pullbackModules).obj G) ×ₘ (pullbackAdjPushforwardModules f).counit.app F)

/-- The canonical map of Stacks 0DK4 is the first bijection of the chain of Stacks 03EL applied
to the comparison `f^*(G ⊗ f_*F) ⟶ f^*G ⊗ f^*f_*F` followed by `tensorCounit`. -/
lemma pushforwardTensorMap_eq_step1 : pushforwardTensorMap f G F =
    pullbackTensorStep1 f G ((pushforwardModules f).obj F)
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
          ((f.pullbackModules).obj G, F))
      (Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom f G
        ((pushforwardModules f).obj F) ≫ tensorCounit f G F) := by
  rw [pushforwardTensorMap_eq]
  unfold Stacks.ProjectionFormula.adjunctionTensorMapSnd
  rw [pullbackTensorIso_hom_app]
  rfl

/-- The canonical map of Stacks 0DK4 is obtained from the pairing `invChainPairing` of
`tensorCounit` by the inverses of the second and third bijections of the chain of Stacks 03EL. -/
lemma pushforwardTensorMap_eq_step2_symm : pushforwardTensorMap f G F =
    (pullbackTensorStep2 f G ((pushforwardModules f).obj F)
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
          ((f.pullbackModules).obj G, F))).symm
      ((pullbackTensorStep3 f G ((pushforwardModules f).obj F)
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
            ((f.pullbackModules).obj G, F))).symm
        (invChainPairing f G ((pushforwardModules f).obj F)
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
              ((f.pullbackModules).obj G, F))
          (tensorCounit f G F))) := by
  rw [pushforwardTensorMap_eq_step1,
    Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom_comp]
  simp only [pullbackTensorHomEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  rfl

/-- **The canonical map `G ⊗ f_*F ⟶ f_*(f^*G ⊗ F)` on a local pure tensor** is the transpose,
across `f⁻¹ ⊣ f_*`, of the pairing of `f⁻¹G` and `f⁻¹f_*F` which steps 4 to 6 of the chain of
Stacks 03EL produce from `f^*G ⊗ f^*f_*F ⟶ f^*G ⊗ F`. -/
lemma pushforwardTensorMap_app_unit_tmul (V : Y.Cᵒᵖ) (a : G.val.obj V)
    (b : ((pushforwardModules f).obj F).val.obj V) :
    (pushforwardTensorMap f G F).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)).unit.app
          (PresheafOfModules.tensorObj G.val ((pushforwardModules f).obj F).val)).app V
          (a ⊗ₜ[(Y.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj V] b)) =
      Stacks.SheafOfModules.pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        (inverseImagePairingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G
          ((pushforwardModules f).obj F)
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
                ((f.pullbackModules).obj G, F)))
          (invChainPairing f G ((pushforwardModules f).obj F)
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
                ((f.pullbackModules).obj G, F))
            (tensorCounit f G F)).1) V a b := by
  have h' := pairingApp_bilinearEquivTensorSheafHom_symm (hA :=
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
    (pushforwardTensorMap f G F) V a b
  refine h'.symm.trans ?_
  rw [pushforwardTensorMap_eq_step2_symm]
  have h₃ := congrArg Subtype.val ((pullbackTensorStep2 f G ((pushforwardModules f).obj F)
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
      ((f.pullbackModules).obj G, F))).apply_symm_apply
    ((pullbackTensorStep3 f G ((pushforwardModules f).obj F)
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
            ((f.pullbackModules).obj G, F))).symm
        (invChainPairing f G ((pushforwardModules f).obj F)
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
              ((f.pullbackModules).obj G, F))
          (tensorCounit f G F))))
  exact congrArg (fun q : Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⨯
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F) ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
                ((f.pullbackModules).obj G, F)))) =>
    Stacks.SheafOfModules.pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q V a b) h₃

end Pairing

section PairingStalk

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

open AlgebraicGeometry.SheafOfModules Stacks.SheafOfModules.RingedToposPullback
open scoped CategoryTheory.Prod

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) (Ψ : Y.J.Point.{w})
  (e : Ψ.sheafFiber (A := Type w) ≅ f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w))
  (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The map `G_Ψ ⟶ (f^*G)_Φ` of stalks: Stacks 05V1 followed by the stalk of the unit of
extension of scalars along the inverse-image form of the structure map. -/
def pullbackStalkHom :
    (Stacks.sheafModuleFiber Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G →+
      (Stacks.sheafModuleFiber Φ
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj ((f.pullbackModules).obj G) :=
  ((Stacks.sheafModuleFiber Φ (inverseImageRingSheaf f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map ((fSharpAdjunction f).unit.app
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          G))).hom.toAddMonoidHom.comp
    (stalkAddEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e G).toAddMonoidHom

omit [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The morphism `f^*G ⊗ f^*f_*F ⟶ f^*G ⊗ F` on the sheafification of a local pure tensor. -/
lemma tensorCounit_val_app_unit_tmul (U : X.Cᵒᵖ) (m : ((f.pullbackModules).obj G).val.obj U)
    (n : ((f.pullbackModules).obj ((pushforwardModules f).obj F)).val.obj U) :
    (tensorCounit f G F).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (PresheafOfModules.tensorObj ((f.pullbackModules).obj G).val
              ((f.pullbackModules).obj ((pushforwardModules f).obj F)).val)).app U
          (m ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] n)) =
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (PresheafOfModules.tensorObj ((f.pullbackModules).obj G).val F.val)).app U
        (m ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U]
          ((pullbackAdjPushforwardModules f).counit.app F).val.app U n) := by
  rw [tensorCounit, Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map]
  exact PresheafOfModules.unit_naturality_apply _ U _

omit [LocallySmall.{w} Y.C] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The stalk of the pairing of steps 4 to 6 of Stacks 03EL on the germ of a pair of sections. -/
lemma tensorSheafModuleFiberIso_hom_germ_invChainPairing (W : X.C) (w : Φ.fiber.obj W)
    (a : (Sheaf.sectionsFunctor X.J (op W)).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)))
    (b : (Sheaf.sectionsFunctor X.J (op W)).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        ((pushforwardModules f).obj F)))) :
    (Stacks.tensorSheafModuleFiberIso Φ X.O ((f.pullbackModules).obj G) F).hom
        (Stacks.toPresheafModuleFiber Φ
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
              ((f.pullbackModules).obj G, F)).val W w
          (Stacks.SheafOfModules.pairingApp
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (invChainPairing f G ((pushforwardModules f).obj F)
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
                  ((f.pullbackModules).obj G, F))
              (tensorCounit f G F)).1 (op W) a b)) =
      Stacks.germ Φ X.O.obj ((f.pullbackModules).obj G).val W w
          (((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
                G)).val.app (op W) a) ⊗ₜ[
          Stacks.ringFiber Φ X.O.obj]
        Stacks.germ Φ X.O.obj F.val W w
          (((pullbackAdjPushforwardModules f).counit.app F).val.app (op W)
            (((structureAdjunction f).unit.app
              ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
                ((pushforwardModules f).obj F))).val.app (op W) b)) := by
  refine (congrArg (fun t => (Stacks.tensorSheafModuleFiberIso Φ X.O ((f.pullbackModules).obj G)
    F).hom (Stacks.toPresheafModuleFiber Φ
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
          ((f.pullbackModules).obj G, F)).val W w t))
    ((pairingApp_invChainPairing f G ((pushforwardModules f).obj F)
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
          ((f.pullbackModules).obj G, F))
      (tensorCounit f G F) (op W) a b).trans
    (tensorCounit_val_app_unit_tmul f G F (op W) _ _))).trans ?_
  exact Stacks.tensorSheafModuleFiberIso_hom_germ Φ X.O _ _ W w _ _

omit [LocallySmall.{w} Y.C] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The stalk of the pairing of steps 4 to 6 of Stacks 03EL**, for the morphism
`f^*G ⊗ f^*f_*F ⟶ f^*G ⊗ F`: on a pair of elements of the stalks at `Φ` of `f⁻¹G` and of
`f⁻¹f_*F` it is, read through the stalk of a tensor product, the pure tensor of the image of the
first in `(f^*G)_Φ` and the image of the second under the counit `f⁻¹f_*F ⟶ F`. -/
lemma tensorSheafModuleFiberIso_hom_map_invChainPairing
    (xa : (Φ.sheafFiber (A := Type w)).obj (f.toToposHom.inverseImage.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)))
    (xb : (Φ.sheafFiber (A := Type w)).obj (f.toToposHom.inverseImage.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((pushforwardModules f).obj F)))) :
    (Stacks.tensorSheafModuleFiberIso Φ X.O ((f.pullbackModules).obj G) F).hom
        (moduleStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
              ((f.pullbackModules).obj G, F))
          ((Φ.sheafFiber (A := Type w)).map
            (invChainPairing f G ((pushforwardModules f).obj F)
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
                  ((f.pullbackModules).obj G, F))
              (tensorCounit f G F)).1
            (Functor.prodObjMk (P := Φ.sheafFiber (A := Type w)) xa xb))) =
      (show (Stacks.sheafModuleFiberOfCommRing Φ X.O).obj ((f.pullbackModules).obj G) from
          (Stacks.sheafModuleFiber Φ (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map ((fSharpAdjunction f).unit.app
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))
            (moduleStalkComparison Φ
                (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) xa)) ⊗ₜ[
          Stacks.ringFiber Φ X.O.obj]
        (show (Stacks.sheafModuleFiberOfCommRing Φ X.O).obj F from
          moduleStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F
            ((Φ.sheafFiber (A := Type w)).map
              (f.toToposHom.adj.counit.app
                  (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F)) xb)) := by
  obtain ⟨W₁, w₁, a₁, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := (f.toToposHom.inverseImage.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).obj) xa
  obtain ⟨W₂, w₂, b₂, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := (f.toToposHom.inverseImage.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj F))).obj) xb
  obtain ⟨W, w, i, j, hi, hj⟩ := Stacks.exists_common_nbhd (Φ := Φ) w₁ w₂
  subst hi hj
  rw [← Φ.toPresheafFiber_w_apply, ← Φ.toPresheafFiber_w_apply]
  refine (congrArg (fun z => (Stacks.tensorSheafModuleFiberIso Φ X.O ((f.pullbackModules).obj G)
      F).hom (moduleStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
            ((f.pullbackModules).obj G, F)) z))
    ((congrArg ((Φ.sheafFiber (A := Type w)).map
        (invChainPairing f G ((pushforwardModules f).obj F)
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
              ((f.pullbackModules).obj G, F))
          (tensorCounit f G F)).1)
      (Φ.prodObjMk_toPresheafFiber W w _ _)).trans
      (Φ.toPresheafFiber_naturality_apply _ W w _))).trans ?_
  refine (congrArg (Stacks.tensorSheafModuleFiberIso Φ X.O ((f.pullbackModules).obj G) F).hom
    (moduleStalkComparison_germ Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O) _ W w _)).trans ?_
  refine (tensorSheafModuleFiberIso_hom_germ_invChainPairing f Φ G F W w _ _).trans ?_
  have hc := congrArg (fun φ => φ.hom.app (op W)
      ((f.toToposHom.inverseImage.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F))).obj.map j.op b₂))
    (moduleSheafFunctor_map_unit_comp_counit f F)
  refine congrArg₂ (fun x y => x ⊗ₜ[Stacks.ringFiber Φ X.O.obj] y) ?_ ?_
  · exact ((congrArg ((Stacks.sheafModuleFiber Φ (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map ((fSharpAdjunction f).unit.app
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)))
      (moduleStalkComparison_germ Φ _ _ W w _)).trans
      (Stacks.toPresheafModuleFiber_naturality Φ _ W w _)).symm
  · refine Eq.trans ?_ (congrArg
      (moduleStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F)
      (Φ.toPresheafFiber_naturality_apply _ W w _)).symm
    refine Eq.trans ?_ (moduleStalkComparison_germ Φ _ _ W w _).symm
    exact congrArg (Stacks.toPresheafModuleFiber Φ F.val W w) hc

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The canonical map of stalks of a direct image, applied to the germ of a value of a pairing
into the direct image, is read off the transpose of that pairing. -/
lemma pushforwardStalkHom_germ_pairingApp (H : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (β : Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⨯ Sheaf.moduleSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) H ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj M))
    (V : Y.C) (v : Ψ.fiber.obj V) (a : G.val.obj (op V)) (b : H.val.obj (op V)) :
    pushforwardStalkHom f Φ Ψ e M (Stacks.toPresheafModuleFiber Ψ ((pushforwardModules f).obj M).val
        V v (Stacks.SheafOfModules.pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) β
            (op V) a b)) =
      moduleStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        ((Φ.sheafFiber (A := Type w)).map ((f.toToposHom.adj.homEquiv _ _).symm β)
          (e.hom.app _ (Ψ.toPresheafFiber V v
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⨯
              Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) H).obj
            (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} Y.J (op V)) a b)))) := by
  have h₁ : Stacks.toPresheafModuleFiber Ψ ((pushforwardModules f).obj M).val
        V v (Stacks.SheafOfModules.pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) β
            (op V) a b) =
      moduleStalkComparison Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M)
        ((Ψ.sheafFiber (A := Type w)).map β (Ψ.toPresheafFiber V v
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⨯
              Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) H).obj
            (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} Y.J (op V)) a b))) :=
    (moduleStalkComparison_germ Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _ V v _).symm.trans
      (congrArg (moduleStalkComparison Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _)
        (Ψ.toPresheafFiber_naturality_apply β.hom V v _).symm)
  rw [h₁, pushforwardStalkHom_moduleStalkComparison]
  exact congrArg (moduleStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
    (f.toToposHom.pushforwardFiberMap_app_map Φ Ψ e β _)

/-- **The stalk of the canonical map of Stacks 0DK4 on the germ of a local pure tensor.** Read
through the stalk of a tensor product at `Φ`, the image of the germ at `Ψ` of `a ⊗ b` under the
stalk of `G ⊗ f_*F ⟶ f_*(f^*G ⊗ F)` followed by `pushforwardStalkHom` is the pure tensor of the
image of the germ of `a` in `(f^*G)_Φ` and the image of the germ of `b` in `F_Φ`. -/
lemma tensorSheafModuleFiberIso_hom_pushforwardStalkHom_map_pushforwardTensorMap
    (V : Y.C) (v : Ψ.fiber.obj V) (a : G.val.obj (op V))
    (b : ((pushforwardModules f).obj F).val.obj (op V)) :
    (Stacks.tensorSheafModuleFiberIso Φ X.O ((f.pullbackModules).obj G) F).hom
        (pushforwardStalkHom f Φ Ψ e
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
              ((f.pullbackModules).obj G, F))
          ((Stacks.sheafModuleFiber Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
              (pushforwardTensorMap f G F)
            (Stacks.toPresheafModuleFiber Ψ
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)).obj
                (G, (pushforwardModules f).obj F)).val V v
              (((PresheafOfModules.sheafificationAdjunction
                  (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)).unit.app
          (PresheafOfModules.tensorObj G.val ((pushforwardModules f).obj F).val)).app
                (op V) (a ⊗ₜ[(Y.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op V)] b))))) =
      (show (Stacks.sheafModuleFiberOfCommRing Φ X.O).obj ((f.pullbackModules).obj G) from
          pullbackStalkHom f Φ Ψ e G (Stacks.toPresheafModuleFiber Ψ G.val V v a)) ⊗ₜ[
          Stacks.ringFiber Φ X.O.obj]
        (show (Stacks.sheafModuleFiberOfCommRing Φ X.O).obj F from
          pushforwardStalkHom f Φ Ψ e F
            (Stacks.toPresheafModuleFiber Ψ ((pushforwardModules f).obj F).val V v b)) := by
  -- the stalk of the canonical map, on the germ of a pure tensor, is the germ of a pairing
  have h₁ := (Stacks.toPresheafModuleFiber_naturality Ψ (pushforwardTensorMap f G F).val V v
      (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)).unit.app
          (PresheafOfModules.tensorObj G.val ((pushforwardModules f).obj F).val)).app
        (op V) (a ⊗ₜ[(Y.O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op V)] b))).trans
    (congrArg (Stacks.toPresheafModuleFiber Ψ ((pushforwardModules f).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
            ((f.pullbackModules).obj G, F))).val V v)
      (pushforwardTensorMap_app_unit_tmul f G F (op V) a b))
  refine (congrArg (fun z => (Stacks.tensorSheafModuleFiberIso Φ X.O
    ((f.pullbackModules).obj G) F).hom
    (pushforwardStalkHom f Φ Ψ e _ z)) h₁).trans ?_
  refine (congrArg (Stacks.tensorSheafModuleFiberIso Φ X.O ((f.pullbackModules).obj G) F).hom
    (pushforwardStalkHom_germ_pairingApp f Φ Ψ e G ((pushforwardModules f).obj F)
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
          ((f.pullbackModules).obj G, F))
      (inverseImagePairingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G
          ((pushforwardModules f).obj F)
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
                ((f.pullbackModules).obj G, F)))
          (invChainPairing f G ((pushforwardModules f).obj F)
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
                ((f.pullbackModules).obj G, F))
            (tensorCounit f G F)).1) V v a b)).trans ?_
  refine (congrArg (fun z => (Stacks.tensorSheafModuleFiberIso Φ X.O ((f.pullbackModules).obj G)
      F).hom (moduleStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
            ((f.pullbackModules).obj G, F)) z))
    (f.toToposHom.map_homEquiv_symm_homEquiv_prodComparison_comp Φ Ψ e
      (invChainPairing f G ((pushforwardModules f).obj F)
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
            ((f.pullbackModules).obj G, F))
        (tensorCounit f G F)).1 _)).trans ?_
  have hz := (Ψ.prodObjMk_toPresheafFiber
      (P := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)
    (Q := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj F)) V v a b).symm
  rw [hz]
  erw [Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]
  refine (tensorSheafModuleFiberIso_hom_map_invChainPairing f Φ G F _ _).trans ?_
  refine congrArg₂ (fun x y => x ⊗ₜ[Stacks.ringFiber Φ X.O.obj] y) ?_ ?_
  · refine congrArg ((Stacks.sheafModuleFiber Φ (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map ((fSharpAdjunction f).unit.app
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
            G))).hom ?_
    exact (stalkModuleMap_moduleStalkComparison f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e G
      _).symm.trans (congrArg
          (stalkModuleMap f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e G)
        (moduleStalkComparison_germ Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G V v a))
  · refine Eq.trans ?_ (congrArg (pushforwardStalkHom f Φ Ψ e F)
      (moduleStalkComparison_germ Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((pushforwardModules f).obj F) V v b))
    exact (pushforwardStalkHom_moduleStalkComparison f Φ Ψ e F _).symm

end PairingStalk

section Criterion

open AlgebraicGeometry.SheafOfModules

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (Ψ : Y.J.Point.{w}) {ι : Type t} [Fintype ι] [DecidableEq ι]
  (Φ : ι → X.J.Point.{w})
  (e : ∀ i, Ψ.sheafFiber (A := Type w) ≅
    f.toToposHom.inverseImage ⋙ (Φ i).sheafFiber (A := Type w))

/-- The canonical maps of stalks of a direct image, assembled into a map to the product, as a
semilinear map over the stalk of the structure sheaf of the target. -/
def pushforwardStalkPiHom (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    letI : ∀ i, Module (Stacks.ringFiber Ψ Y.O.obj)
        ((Stacks.sheafModuleFiberOfCommRing (Φ i) X.O).obj N) := fun i =>
      Module.compHom _ (Stacks.Sheaves.StalkPullback.stalkRingMap f (Φ i) Ψ (e i))
    (Stacks.sheafModuleFiberOfCommRing Ψ Y.O).obj ((pushforwardModules f).obj N) →ₗ[
        Stacks.ringFiber Ψ Y.O.obj] ∀ i, (Stacks.sheafModuleFiberOfCommRing (Φ i) X.O).obj N :=
  letI : ∀ i, Module (Stacks.ringFiber Ψ Y.O.obj)
      ((Stacks.sheafModuleFiberOfCommRing (Φ i) X.O).obj N) := fun i =>
    Module.compHom _ (Stacks.Sheaves.StalkPullback.stalkRingMap f (Φ i) Ψ (e i))
  { toFun := fun z i => pushforwardStalkHom f (Φ i) Ψ (e i) N z
    map_add' := fun z z' => funext fun i => (pushforwardStalkHom f (Φ i) Ψ (e i) N).map_add z z'
    map_smul' := fun r z => funext fun i => pushforwardStalkHom_smul f (Φ i) Ψ (e i) N r z }

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Fintype ι] [DecidableEq ι] in
/-- On underlying stalks of sheaves of sets, the components of `pushforwardStalkPiHom` are the
maps `MorphismOfTopoi.pushforwardFiberMap` at the points `Φ i`. -/
lemma pushforwardStalkPiHom_moduleStalkComparison (N : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (x : (Ψ.sheafFiber (A := Type w)).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((pushforwardModules f).obj N))) :
    pushforwardStalkPiHom f Ψ Φ e N (moduleStalkComparison Ψ
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _ x) =
      fun i => moduleStalkComparison (Φ i) (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N
        ((f.toToposHom.pushforwardFiberMap (Φ i) Ψ (e i)).app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) x) :=
  funext fun i => pushforwardStalkHom_moduleStalkComparison f (Φ i) Ψ (e i) N x

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Fintype ι] [DecidableEq ι] in
/-- **The stalk of a direct image of modules is the product of the stalks**, as soon as this
holds for sheaves of sets. -/
lemma bijective_pushforwardStalkPiHom
    (h : ∀ F : Sheaf X.J (Type w), Function.Bijective
      (fun z i => (f.toToposHom.pushforwardFiberMap (Φ i) Ψ (e i)).app F z))
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Function.Bijective (pushforwardStalkPiHom f Ψ Φ e N) := by
  have hc : (pushforwardStalkPiHom f Ψ Φ e N) ∘
      moduleStalkComparison Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj N) =
      (fun (y : ∀ i, (Φ i).sheafFiber.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) i =>
        moduleStalkComparison (Φ i) (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N (y i)) ∘
      (fun z i => (f.toToposHom.pushforwardFiberMap (Φ i) Ψ (e i)).app
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) z) :=
    funext fun x => pushforwardStalkPiHom_moduleStalkComparison f Ψ Φ e N x
  have h₂ := (Function.Bijective.piMap fun i => bijective_moduleStalkComparison (Φ i) _ N).comp
    (h _)
  exact (Function.Bijective.of_comp_iff _ (bijective_moduleStalkComparison Ψ _ _)).1
    ((congrArg Function.Bijective hc).mpr h₂)

/-- The ring map `𝒪'_Ψ ⟶ 𝒪_{Φ i}` of Stacks 05V5, as an algebra structure. -/
abbrev stalkAlgebra (i : ι) :
    Algebra (Stacks.ringFiber Ψ Y.O.obj) (Stacks.ringFiber (Φ i) X.O.obj) :=
  (Stacks.Sheaves.StalkPullback.stalkRingMap f (Φ i) Ψ (e i)).toAlgebra

/-- The scalars of `𝒪'_Ψ` on a stalk at `Φ i`, through `𝒪'_Ψ ⟶ 𝒪_{Φ i}`. -/
abbrev stalkModuleOfStalkRingMap (i : ι) (N : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Module (Stacks.ringFiber Ψ Y.O.obj) ((Stacks.sheafModuleFiberOfCommRing (Φ i) X.O).obj N) :=
  Module.compHom _ (Stacks.Sheaves.StalkPullback.stalkRingMap f (Φ i) Ψ (e i))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Fintype ι] [DecidableEq ι] in
/-- The scalars `𝒪'_Ψ → 𝒪_{Φ i}` on a stalk at `Φ i` form a scalar tower. -/
lemma stalkModuleOfStalkRingMap_isScalarTower (i : ι)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    letI := stalkAlgebra f Ψ Φ e i
    letI := stalkModuleOfStalkRingMap f Ψ Φ e i N
    IsScalarTower (Stacks.ringFiber Ψ Y.O.obj) (Stacks.ringFiber (Φ i) X.O.obj)
      ((Stacks.sheafModuleFiberOfCommRing (Φ i) X.O).obj N) :=
  let := stalkAlgebra f Ψ Φ e i
  let := stalkModuleOfStalkRingMap f Ψ Φ e i N
  ⟨fun _ a m => mul_smul _ a m⟩

/-- **Stacks 05V5 at `(Φ i, Ψ)` as a base change**: the stalk at `Φ i` of `f^*G` is
`𝒪_{Φ i} ⊗_{𝒪'_Ψ} G_Ψ`. -/
def stalkBaseChangeEquiv (i : ι) (G : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    letI := stalkAlgebra f Ψ Φ e i
    (Stacks.ringFiber (Φ i) X.O.obj ⊗[Stacks.ringFiber Ψ Y.O.obj]
        (Stacks.sheafModuleFiberOfCommRing Ψ Y.O).obj G) ≃ₗ[Stacks.ringFiber (Φ i) X.O.obj]
      (Stacks.sheafModuleFiberOfCommRing (Φ i) X.O).obj ((f.pullbackModules).obj G) :=
  letI := stalkAlgebra f Ψ Φ e i
  ((Stacks.TensorProductPushout.extendScalarsObjIso'
      (Stacks.Sheaves.StalkPullback.stalkRingMap f (Φ i) Ψ (e i)) rfl
      ((Stacks.sheafModuleFiberOfCommRing Ψ Y.O).obj G)).symm ≪≫
    ((Stacks.Sheaves.StalkPullback.stalkFunctorIso f (Φ i) Ψ (e i)).app G).symm).toLinearEquiv

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Fintype ι] [DecidableEq ι] in
/-- On `1 ⊗ g`, the base-change identification `stalkBaseChangeEquiv` is the map
`G_Ψ ⟶ (f^*G)_{Φ i}` of stalks. -/
lemma stalkBaseChangeEquiv_one_tmul (i : ι) (G : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (g : (Stacks.sheafModuleFiberOfCommRing Ψ Y.O).obj G) :
    letI := stalkAlgebra f Ψ Φ e i
    stalkBaseChangeEquiv f Ψ Φ e i G ((1 : Stacks.ringFiber (Φ i) X.O.obj) ⊗ₜ g) =
      pullbackStalkHom f (Φ i) Ψ (e i) G g :=
  stalkFunctorIso_inv_app_one_tmul f (Φ i) Ψ (e i) G g

omit [Fintype ι] [DecidableEq ι] in
/-- **The stalk at `Ψ` of the canonical map `G ⊗ f_*F ⟶ f_*(f^*G ⊗ F)` is an isomorphism**
as soon as the stalk at `Ψ` of a direct image of sheaves of sets is the product of the stalks at
finitely many points `Φ i` of the source, each identified with `Ψ` along `f`. -/
theorem isIso_sheafModuleFiberOfCommRing_map_pushforwardTensorMap [Finite ι]
    (h : ∀ M : Sheaf X.J (Type w), Function.Bijective
      (fun z i => (f.toToposHom.pushforwardFiberMap (Φ i) Ψ (e i)).app M z))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsIso ((Stacks.sheafModuleFiberOfCommRing Ψ Y.O).map (pushforwardTensorMap f G F)) := by
  classical
  have := Fintype.ofFinite ι
  let := fun i => stalkAlgebra f Ψ Φ e i
  let := fun i => stalkModuleOfStalkRingMap f Ψ Φ e i F
  let := fun i => stalkModuleOfStalkRingMap f Ψ Φ e i ((f.pullbackModules).obj G)
  have := fun i => stalkModuleOfStalkRingMap_isScalarTower f Ψ Φ e i F
  have := fun i =>
    stalkModuleOfStalkRingMap_isScalarTower f Ψ Φ e i ((f.pullbackModules).obj G)
  let Θ := TensorProduct.tensorPiBaseChangeEquiv (Stacks.ringFiber Ψ Y.O.obj)
    ((Stacks.sheafModuleFiberOfCommRing Ψ Y.O).obj G) (fun i => Stacks.ringFiber (Φ i) X.O.obj)
    (fun i => (Stacks.sheafModuleFiberOfCommRing (Φ i) X.O).obj ((f.pullbackModules).obj G))
    (fun i => (Stacks.sheafModuleFiberOfCommRing (Φ i) X.O).obj F)
    (fun i => stalkBaseChangeEquiv f Ψ Φ e i G)
  let ψF := LinearEquiv.ofBijective (pushforwardStalkPiHom f Ψ Φ e F)
    (bijective_pushforwardStalkPiHom f Ψ Φ e h F)
  let TY := (Stacks.tensorSheafModuleFiberIso Ψ Y.O G ((pushforwardModules f).obj F)).toLinearEquiv
  have key : ∀ x, (fun i => (Stacks.tensorSheafModuleFiberIso (Φ i) X.O ((f.pullbackModules).obj G)
        F).hom (pushforwardStalkPiHom f Ψ Φ e
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
              ((f.pullbackModules).obj G, F))
          ((Stacks.sheafModuleFiberOfCommRing Ψ Y.O).map (pushforwardTensorMap f G F)
            (TY.symm x)) i)) =
      Θ (LinearEquiv.lTensor ((Stacks.sheafModuleFiberOfCommRing Ψ Y.O).obj G) ψF x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      funext i
      have hx' := congrFun hx i
      have hy' := congrFun hy i
      simp only [map_add, Pi.add_apply] at hx' hy' ⊢
      rw [hx', hy']
    | tmul g z =>
      obtain ⟨V₁, v₁, a₁, rfl⟩ := Stacks.toPresheafModuleFiber_jointly_surjective Ψ G.val g
      obtain ⟨V₂, v₂, b₂, rfl⟩ := Stacks.toPresheafModuleFiber_jointly_surjective Ψ
        ((pushforwardModules f).obj F).val z
      obtain ⟨W, w, i₁, i₂, h₁, h₂⟩ := Stacks.exists_common_nbhd (Φ := Ψ) v₁ v₂
      subst h₁ h₂
      rw [Stacks.toPresheafModuleFiber_w, Stacks.toPresheafModuleFiber_w]
      have hTY := Stacks.tensorSheafModuleFiberIso_hom_germ Ψ Y.O G ((pushforwardModules f).obj F)
        W w (G.val.map i₁.op a₁) (((pushforwardModules f).obj F).val.map i₂.op b₂)
      have hTY' : TY.symm (Stacks.toPresheafModuleFiber Ψ G.val W w (G.val.map i₁.op a₁) ⊗ₜ[
          Stacks.ringFiber Ψ Y.O.obj] Stacks.toPresheafModuleFiber Ψ
            ((pushforwardModules f).obj F).val W w
            (((pushforwardModules f).obj F).val.map i₂.op b₂)) = _ :=
        (LinearEquiv.symm_apply_eq TY).2 hTY.symm
      rw [hTY']
      funext i
      refine (tensorSheafModuleFiberIso_hom_pushforwardStalkHom_map_pushforwardTensorMap f (Φ i) Ψ
        (e i) G F W w _ _).trans ?_
      refine Eq.symm ((congrArg (fun y => Θ y i) (LinearEquiv.lTensor_tmul _ _ _ _)).trans ?_)
      refine (TensorProduct.tensorPiBaseChangeEquiv_tmul _ _ _ _ _ _ _ _ i).trans ?_
      exact congrArg (fun y => y ⊗ₜ[Stacks.ringFiber (Φ i) X.O.obj] _)
        (stalkBaseChangeEquiv_one_tmul f Ψ Φ e i G _)
  have hP : Function.Bijective (fun y i => (Stacks.tensorSheafModuleFiberIso (Φ i) X.O
      ((f.pullbackModules).obj G) F).hom (pushforwardStalkPiHom f Ψ Φ e
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
            ((f.pullbackModules).obj G, F)) y i)) :=
    (Function.Bijective.piMap fun i => (ConcreteCategory.isIso_iff_bijective _).1
      (inferInstance : IsIso (Stacks.tensorSheafModuleFiberIso (Φ i) X.O
        ((f.pullbackModules).obj G) F).hom)).comp (bijective_pushforwardStalkPiHom f Ψ Φ e h _)
  have hR : Function.Bijective (((fun y i => (Stacks.tensorSheafModuleFiberIso (Φ i) X.O
      ((f.pullbackModules).obj G) F).hom (pushforwardStalkPiHom f Ψ Φ e
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj
            ((f.pullbackModules).obj G, F)) y i)) ∘
      ((Stacks.sheafModuleFiberOfCommRing Ψ Y.O).map (pushforwardTensorMap f G F))) ∘
        TY.symm) := by
    exact (congrArg Function.Bijective (funext key)).mpr
      (Θ.bijective.comp (LinearEquiv.lTensor _ ψF).bijective)
  rw [ConcreteCategory.isIso_iff_bijective]
  have h₁ := (Function.Bijective.of_comp_iff _ TY.symm.bijective).1 hR
  exact (Function.Bijective.of_comp_iff' hP _).1 h₁

omit [Fintype ι] [DecidableEq ι] in
/-- **The canonical map `G ⊗ f_*F ⟶ f_*(f^*G ⊗ F)` is an isomorphism** when the target site
has a conservative family of points at each of which the stalk of a direct image of sheaves of
sets is the product of the stalks at finitely many points of the source, each identified with
it along `f`. -/
theorem isIso_pushforwardTensorMap_of_isConservativeFamilyOfPoints
    {P : ObjectProperty Y.J.Point.{w}} (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ Ψ : Y.J.Point.{w}, P Ψ → ∃ (ι : Type w) (_ : Finite ι) (Φ : ι → X.J.Point.{w})
      (e : ∀ i, Ψ.sheafFiber (A := Type w) ≅
        f.toToposHom.inverseImage ⋙ (Φ i).sheafFiber (A := Type w)),
      ∀ M : Sheaf X.J (Type w), Function.Bijective
        (fun z i => (f.toToposHom.pushforwardFiberMap (Φ i) Ψ (e i)).app M z))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsIso (pushforwardTensorMap f G F) := by
  refine Stacks.isIso_of_isIso_sheafModuleFiber (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) hP _
    fun Ψ => ?_
  obtain ⟨ι, _, Φ, e, hΦ⟩ := h Ψ.obj Ψ.property
  have hi := isIso_sheafModuleFiberOfCommRing_map_pushforwardTensorMap f Ψ.obj Φ e hΦ G F
  rw [ConcreteCategory.isIso_iff_bijective] at hi ⊢
  exact hi

end Criterion

end Stacks.SheafOfModules

end
