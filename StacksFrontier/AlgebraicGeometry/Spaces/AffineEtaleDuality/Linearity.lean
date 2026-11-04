module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.Sections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# `A`-linearity of `ε^*T` and smallness of internal Hom sections

Two facts used to build the comparison map of Stacks 0E50.

* Multiplication by a global section of the structure sheaf is an endomorphism of every
  `𝒪_étale`-module, and `ε^*T` carries multiplication by `a ∈ A` on a linear map to
  multiplication by the global section `ρ(a)`.
* On an essentially small ringed site, the sections of every term of the internal Hom complex of
  two complexes of `SheafOfModules.{m}` are `m`-small.

## Main definitions

* `AlgebraicGeometry.AffineEtaleDuality.smulEnd`: multiplication by a global section.

## Main results

* `AlgebraicGeometry.AffineEtaleDuality.epsT_map_smul`.
* `AlgebraicGeometry.RingedSite.small_sheafHomComplex_obj`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u c

namespace AlgebraicGeometry.RingedSite

/-- **The sections of the internal Hom complex are small** on an essentially small ringed
site. -/
instance small_sheafHomComplex_obj (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) (Y : X.Cᵒᵖ) :
    Small.{u} (((sheafHomComplex X L M).obj.X n).val.obj Y) := by
  have := Stacks.essentiallySmall_over.{u} Y.unop
  have := Stacks.locallySmall_presheafOfModules_of_essentiallySmall.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Y.unop).obj
  have : ∀ p q : ℤ, Small.{u} ((restrictComplex X L Y.unop).X p ⟶
      (restrictComplex X M Y.unop).X q) := fun p q =>
    small_of_injective (f := fun g => g.val) (fun g h hgh => SheafOfModules.hom_ext hgh)
  have : Small.{u} (((restrictComplex X L Y.unop).HomComplex (restrictComplex X M Y.unop)).X n) :=
    inferInstanceAs (Small.{u} (∀ T : Triplet n, _))
  exact small_of_injective (f := ((sheafHomComplex X L M).sectionsIso Y.unop).hom.f n)
    (ConcreteCategory.injective_of_mono_of_preservesPullback _)

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.AffineEtaleDuality

variable (A : CommRingCat.{u}) (B : BigEtaleSite.{u}) (hX : B.Contains (Spec A))

/-- The sections of the structure sheaf `𝒪` over any object of the site commute. -/
lemma O_mul_comm (W : Site A B hX) (r s : (O A B hX).obj.obj (op W)) : r * s = s * r :=
  mul_comm (G := (Rc A B hX).obj (op W)) r s

/-- **Multiplication by a global section of `𝒪` is an endomorphism of every `𝒪`-module.** -/
def smulEnd (E : Mod A B hX) (r : (O A B hX).obj.obj (op (top A B hX))) : E ⟶ E where
  val :=
    { app := fun W => ModuleCat.ofHom
        { toFun := fun x => (O A B hX).obj.map (toTop A B hX W.unop).op r • x
          map_add' := fun x y => smul_add _ x y
          map_smul' := fun s x => by
            change _ • (s • x) = s • (_ • x)
            rw [smul_smul, smul_smul, O_mul_comm] }
      naturality := fun {W W'} g => by
        ext x
        change (O A B hX).obj.map (toTop A B hX W'.unop).op r • E.val.map g x =
          E.val.map g ((O A B hX).obj.map (toTop A B hX W.unop).op r • x)
        rw [PresheafOfModules.map_smul]
        congr 1
        symm
        have hg : (toTop A B hX W.unop).op ≫ g = (toTop A B hX W'.unop).op :=
          Quiver.Hom.unop_inj (toTop_eq A B hX _)
        change ((O A B hX).obj.map (toTop A B hX W.unop).op ≫ (O A B hX).obj.map g).hom r = _
        rw [← Functor.map_comp, hg] }

/-- On sections over `W`, `smulEnd E r` multiplies by the restriction of `r` to `W`. -/
lemma smulEnd_val_app (E : Mod A B hX) (r : (O A B hX).obj.obj (op (top A B hX)))
    (W : Site A B hX) (x : E.val.obj (op W)) :
    (smulEnd A B hX E r).val.app (op W) x = (O A B hX).obj.map (toTop A B hX W).op r • x := rfl

/-- Multiplication by a global section of `𝒪` commutes with every morphism of `𝒪`-modules. -/
lemma smulEnd_naturality {E E' : Mod A B hX} (f : E ⟶ E')
    (r : (O A B hX).obj.obj (op (top A B hX))) :
    smulEnd A B hX E r ≫ f = f ≫ smulEnd A B hX E' r := by
  ext W x
  show f.val.app W ((O A B hX).obj.map (toTop A B hX W.unop).op r • x) =
    (O A B hX).obj.map (toTop A B hX W.unop).op r • f.val.app W x
  exact map_smul (f.val.app W).hom _ x

/-- Restricting a global section of `𝒪` along the identity of the top object returns it. -/
lemma O_map_toTop_top (r : (O A B hX).obj.obj (op (top A B hX))) :
    (O A B hX).obj.map (toTop A B hX (top A B hX)).op r = r := by
  rw [← toTop_eq A B hX (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **`ε^*T` is `A`-linear**: it carries `a • h` to `ε^*T h` followed by multiplication by the
global section `ρ(a)`. -/
lemma epsT_map_smul {M N : ModuleCat.{u} A} (h : M ⟶ N) (a : A) :
    (epsT A B hX).map (a • h) =
      (epsT A B hX).map h ≫ smulEnd A B hX ((epsT A B hX).obj N) (ρtop A B hX a) := by
  apply ((epsTAdj A B hX).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext m
  have h1 := congrArg (fun g => g.hom m) ((epsTAdj A B hX).unit.naturality (a • h))
  have h2 := congrArg (fun g => g.hom m) ((epsTAdj A B hX).unit.naturality h)
  change ((epsTAdj A B hX).unit.app N).hom ((a • h).hom m) = _ at h1
  refine h1.symm.trans ?_
  show ((epsTAdj A B hX).unit.app N).hom (a • h.hom m) = (smulEnd A B hX ((epsT A B hX).obj N)
    (ρtop A B hX a)).val.app (op (top A B hX))
      (((epsT A B hX).map h).val.app (op (top A B hX)) (((epsTAdj A B hX).unit.app M).hom m))
  rw [map_smul, smulEnd_val_app, O_map_toTop_top]
  show _ = ρtop A B hX a • (show ((epsT A B hX).obj N).val.obj (op (top A B hX)) from
    ((gammaTop A B hX).map ((epsT A B hX).map h)).hom (((epsTAdj A B hX).unit.app M).hom m))
  exact congrArg (fun y => ρtop A B hX a •
    (show ((epsT A B hX).obj N).val.obj (op (top A B hX)) from y)) h2

end AlgebraicGeometry.AffineEtaleDuality

end
