module

public import Mathlib.RingTheory.LocalRing.Length
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a direct image along the fibre of the support

Let `f : X ⟶ Y` be a closed morphism of schemes and let `F` be an `𝒪_X`-module whose support is
closed and whose irreducible components form a locally finite family. If every point of
`Supp(F)` lying over `y ∈ Y` is the generic point of an irreducible component of `Supp(F)`, then
the stalk of `f_* F` at `y` is the product of the stalks of `F` at those points,

  `(f_* F)_y ≅ ∏_{x ∈ Supp(F) ∩ f⁻¹(y)} F_x`,

as modules over `𝒪_{Y,y}`.

## Main definitions

* `Stacks.Chow.fibreStalkComparison`, `Stacks.Chow.supportFibreStalkLinearMap` — the comparison
  from the stalk of `f_* F` at `y` to the stalk of `F` at a point of the fibre, as a map of
  abelian groups and as an `𝒪_{Y,y}`-linear map.
* `Stacks.Chow.pushforwardStalkLinearEquivPi` — the product decomposition of the stalk.

## Main results

* `Stacks.Chow.supp_pushforward_subset_image` — the support of a direct image along a closed
  morphism is contained in the image of the support.
* `Stacks.Chow.eq_zero_of_forall_fibreStalkComparison_eq_zero` — a germ of `f_* F` at `y` all of
  whose components along the fibre of the support vanish is zero.
* `Stacks.Chow.exists_fibreStalkComparison_eq` — prescribed germs along the fibre of the support
  are realized by a germ of `f_* F` at `y`.
* `Stacks.Chow.length_stalk_restrictScalars_toNat` — the length of a stalk of `F` over
  `𝒪_{Y,y}` is its length over `𝒪_{X,x}` times the residue degree of `f` at `x`.

## References

* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}}

/-! ### Sections away from the support -/

/-- The stalk of a sheaf of modules at a point outside its support is trivial. -/
private theorem subsingleton_stalk_of_notMem_supp (F : X.Modules) {x : X}
    (hx : x ∉ SheafOfModules.supp F) : Subsingleton (F.presheaf.stalk x) :=
  not_nontrivial_iff_subsingleton.mp fun hn =>
    hx ((SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mpr hn)

/-- A sheaf of modules has only the zero section over an open disjoint from its support. -/
theorem subsingleton_sections_of_forall_notMem_supp (F : X.Modules) (U : X.Opens)
    (hU : ∀ x ∈ U, x ∉ SheafOfModules.supp F) : Subsingleton (F.presheaf.obj (op U)) := by
  refine ⟨fun s t => ?_⟩
  apply TopCat.Presheaf.section_ext ⟨F.presheaf, Scheme.Modules.isSheaf F⟩ U s t
  intro x hx
  have := subsingleton_stalk_of_notMem_supp F (hU x hx)
  exact Subsingleton.elim _ _

/-- The support of a direct image along a closed morphism is contained in the image of the
support. -/
theorem supp_pushforward_subset_image (f : X ⟶ Y) [UniversallyClosed f] (F : X.Modules)
    (hF : IsClosed (SheafOfModules.supp F)) :
    SheafOfModules.supp ((Scheme.Modules.pushforward f).obj F) ⊆
      f.base '' SheafOfModules.supp F := by
  intro y hy
  by_contra hyimage
  have himageClosed : IsClosed (f.base '' SheafOfModules.supp F) := f.isClosedMap _ hF
  let U : Y.Opens := ⟨(f.base '' SheafOfModules.supp F)ᶜ, himageClosed.isOpen_compl⟩
  have hyU : y ∈ U := hyimage
  let G := (Scheme.Modules.pushforward f).obj F
  obtain ⟨a, ha⟩ := hy
  obtain ⟨V, hyV, s, hs⟩ := G.presheaf.exists_germ_eq a
  have hane : G.presheaf.germ V y hyV s ≠ 0 := hs ▸ ha
  let W := V ⊓ U
  have hyW : y ∈ W := ⟨hyV, hyU⟩
  have hW : W ≤ V := inf_le_left
  have hsections : Subsingleton (G.presheaf.obj (op W)) :=
    subsingleton_sections_of_forall_notMem_supp F (f ⁻¹ᵁ W) fun x hx hxF =>
      (show f x ∈ W from hx).2 ⟨x, hxF, rfl⟩
  apply hane
  rw [← G.presheaf.germ_res_apply (homOfLE hW) y hyW s,
    hsections.elim (G.presheaf.map (homOfLE hW).op s) 0]
  simp

/-! ### The comparison with the stalks along the fibre -/

/-- The comparison map from the stalk of `f_* F` at `y` to the stalk of `F` at a point of the
fibre over `y`. -/
def fibreStalkComparison (f : X ⟶ Y) (F : X.Modules) (y : Y) (x : X) (hxy : f x = y) :
    ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y → F.presheaf.stalk x := by
  subst hxy
  exact stalkPushforwardComparison f F x

/-- The comparison map sends the germ at `y` of a section of `f_* F` over `U` to the germ at the
fibre point of that same section, read over `f⁻¹ U`. -/
theorem fibreStalkComparison_germ (f : X ⟶ Y) (F : X.Modules) (y : Y) (x : X) (hxy : f x = y)
    (U : Y.Opens) (hy : y ∈ U) (s : Γ(F, f ⁻¹ᵁ U)) :
    fibreStalkComparison f F y x hxy
        (((Scheme.Modules.pushforward f).obj F).presheaf.germ U y hy s) =
      F.presheaf.germ (f ⁻¹ᵁ U) x (show f x ∈ U by rw [hxy]; exact hy) s := by
  subst hxy
  exact stalkPushforwardComparison_germ f F x U hy s

/-- The comparison map is additive. -/
theorem fibreStalkComparison_add (f : X ⟶ Y) (F : X.Modules) (y : Y) (x : X) (hxy : f x = y)
    (a b : ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y) :
    fibreStalkComparison f F y x hxy (a + b) =
      fibreStalkComparison f F y x hxy a + fibreStalkComparison f F y x hxy b := by
  subst hxy
  exact stalkPushforwardComparison_add f F x a b

/-- The comparison map respects differences. -/
theorem fibreStalkComparison_sub (f : X ⟶ Y) (F : X.Modules) (y : Y) (x : X) (hxy : f x = y)
    (a b : ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y) :
    fibreStalkComparison f F y x hxy (a - b) =
      fibreStalkComparison f F y x hxy a - fibreStalkComparison f F y x hxy b := by
  subst hxy
  exact map_sub (TopCat.Presheaf.stalkPushforward Ab.{u} f.base F.val.presheaf x).hom a b

/-- The comparison map at a point `x` of `X`, as a map linear over the local ring of `Y` at
`f x` acting through the stalk map of `f`. -/
def stalkLinearMapOverBase (f : X ⟶ Y) (F : X.Modules) (x : X) :
    letI : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
      Module.compHom _ (f.stalkMap x).hom
    ((Scheme.Modules.pushforward f).obj F).presheaf.stalk (f x) →ₗ[Y.presheaf.stalk (f x)]
      F.presheaf.stalk x :=
  letI : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  { toFun := stalkPushforwardComparison f F x
    map_add' := stalkPushforwardComparison_add f F x
    map_smul' := stalkPushforwardComparison_smul f F x }

/-! ### The product decomposition of the stalk -/

/-- For a closed morphism and an open `A` of `X`, there is an open of `Y` containing exactly the
points whose support fibre lies in `A`, and whose preimage meets the support only in `A`. -/
private theorem exists_opens_supp_preimage_subset (f : X ⟶ Y) [UniversallyClosed f]
    (F : X.Modules) (hclosed : IsClosed (SheafOfModules.supp F)) (A : X.Opens) :
    ∃ V : Y.Opens, (∀ y, (∀ z ∈ SheafOfModules.supp F, f z = y → z ∈ A) → y ∈ V) ∧
      ∀ z ∈ SheafOfModules.supp F, f z ∈ V → z ∈ A :=
  ⟨⟨(f '' (SheafOfModules.supp F \ (A : Set X)))ᶜ,
    (f.isClosedMap _ (hclosed.inter A.isOpen.isClosed_compl)).isOpen_compl⟩,
    fun _ h ⟨z, ⟨hzF, hzA⟩, hzy⟩ => hzA (h z hzF hzy),
    fun z hzF hz => of_not_not fun hn => hz ⟨z, ⟨hzF, hn⟩, rfl⟩⟩

/-- A germ of `f_* F` at `y` whose comparison to the stalk of `F` vanishes at every point of the
support lying over `y` is zero, provided `f` is closed. -/
theorem eq_zero_of_forall_fibreStalkComparison_eq_zero (f : X ⟶ Y) [UniversallyClosed f]
    (F : X.Modules) (hclosed : IsClosed (SheafOfModules.supp F)) (y : Y)
    (t : ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y)
    (ht : ∀ (x : X) (hxy : f x = y), x ∈ SheafOfModules.supp F →
      fibreStalkComparison f F y x hxy t = 0) : t = 0 := by
  classical
  let G := (Scheme.Modules.pushforward f).obj F
  obtain ⟨U, hyU, s, rfl⟩ := G.presheaf.exists_germ_eq t
  let P (W : X.Opens) : Prop := ∃ h : W ≤ f ⁻¹ᵁ U,
    F.presheaf.map (homOfLE h).op s = 0
  let A : X.Opens := ⨆ W : {W : X.Opens // P W}, W.1
  have hA (x : X) (hxy : f x = y) (hx : x ∈ SheafOfModules.supp F) : x ∈ A := by
    have hxU : x ∈ f ⁻¹ᵁ U := show f x ∈ U by rw [hxy]; exact hyU
    have hg : F.presheaf.germ (f ⁻¹ᵁ U) x hxU s = F.presheaf.germ (f ⁻¹ᵁ U) x hxU 0 := by
      rw [map_zero, ← fibreStalkComparison_germ f F y x hxy U hyU s, ht x hxy hx]
    obtain ⟨W, hxW, iW, _, he⟩ := F.presheaf.germ_eq x hxU hxU s 0 hg
    exact (le_iSup (fun W : {W : X.Opens // P W} => W.1)
      ⟨W, leOfHom iW, by change F.presheaf.map iW.op s = 0; simpa only [map_zero] using he⟩) hxW
  obtain ⟨V₀, hV₀, hV₀A⟩ := exists_opens_supp_preimage_subset f F hclosed A
  let V : Y.Opens := U ⊓ V₀
  have hyV : y ∈ V := ⟨hyU, hV₀ y fun x hxF hxy => hA x hxy hxF⟩
  have hVU : V ≤ U := inf_le_left
  have hpre : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U := fun x hx => hVU hx
  have hres : F.presheaf.map (homOfLE hpre).op s = 0 := by
    apply TopCat.Presheaf.section_ext ⟨F.presheaf, Scheme.Modules.isSheaf F⟩
    intro x hx
    by_cases hxF : x ∈ SheafOfModules.supp F
    · have hxA : x ∈ A := hV₀A x hxF (show f x ∈ V from hx).2
      obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp hxA
      obtain ⟨hW, he⟩ := W.2
      rw [map_zero, F.presheaf.germ_res_apply (homOfLE hpre) x hx s,
        ← F.presheaf.germ_res_apply (homOfLE hW) x hxW s, he, map_zero]
    · have := subsingleton_stalk_of_notMem_supp F hxF
      exact Subsingleton.elim _ _
  calc
    G.presheaf.germ U y hyU s =
        G.presheaf.germ V y hyV (G.presheaf.map (homOfLE hVU).op s) :=
      (G.presheaf.germ_res_apply (homOfLE hVU) y hyV s).symm
    _ = 0 := by
      show G.presheaf.germ V y hyV (F.presheaf.map (homOfLE hpre).op s) = 0
      rw [hres]
      exact map_zero _

/-- Germs of `F` prescribed at the points of the support lying over `y` are realized by a germ of
`f_* F` at `y`, provided `f` is closed and those points are separated by opens meeting the
support only in their own. -/
theorem exists_fibreStalkComparison_eq (f : X ⟶ Y) [UniversallyClosed f] (F : X.Modules)
    (hclosed : IsClosed (SheafOfModules.supp F)) (y : Y) {ι : Type u} (x : ι → X)
    (hxy : ∀ a, f (x a) = y)
    (hcover : ∀ z ∈ SheafOfModules.supp F, f z = y → ∃ a, x a = z)
    (E : ι → X.Opens) (hE : ∀ a, x a ∈ E a)
    (hdis : ∀ a b, a ≠ b → ∀ z, z ∈ E a → z ∈ E b → z ∉ SheafOfModules.supp F)
    (m : ∀ a, F.presheaf.stalk (x a)) :
    ∃ t : ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y,
      ∀ a, fibreStalkComparison f F y (x a) (hxy a) t = m a := by
  classical
  choose U hUE hxU s hs using fun a => F.presheaf.exists_le_germ_eq (m a) (hE a)
  let A : X.Opens := ⨆ a, U a
  obtain ⟨V, hV, hVA⟩ := exists_opens_supp_preimage_subset f F hclosed A
  have hyV : y ∈ V := hV y fun z hzF hzy => by
    obtain ⟨a, rfl⟩ := hcover z hzF hzy
    exact (le_iSup U a) (hxU a)
  let O : Option ι → X.Opens
    | none => (f ⁻¹ᵁ V) ⊓ ⟨(SheafOfModules.supp F)ᶜ, hclosed.isOpen_compl⟩
    | some a => (f ⁻¹ᵁ V) ⊓ U a
  have hOV (a : Option ι) : O a ≤ f ⁻¹ᵁ V := by cases a <;> exact inf_le_left
  have hcov : f ⁻¹ᵁ V ≤ ⨆ a, O a := by
    intro z hz
    by_cases hzF : z ∈ SheafOfModules.supp F
    · have hzA : z ∈ A := hVA z hzF hz
      obtain ⟨a, hza⟩ := Opens.mem_iSup.mp hzA
      exact (le_iSup O (some a)) ⟨hz, hza⟩
    · exact (le_iSup O none) ⟨hz, hzF⟩
  let sO : ∀ a, F.presheaf.obj (op (O a))
    | none => 0
    | some a => F.presheaf.map (homOfLE (show O (some a) ≤ U a from inf_le_right)).op (s a)
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf O sO := by
    intro a b
    by_cases hab : a = b
    · subst b; rfl
    · have hsub : Subsingleton (F.presheaf.obj (op (O a ⊓ O b))) := by
        refine subsingleton_sections_of_forall_notMem_supp F (O a ⊓ O b) fun z hz => ?_
        cases a with
        | none => exact hz.1.2
        | some a =>
          cases b with
          | none => exact hz.2.2
          | some b =>
            exact hdis a b (fun h => hab (congrArg some h)) z
              (hUE a hz.1.2) (hUE b hz.2.2)
      exact hsub.elim _ _
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨F.presheaf, Scheme.Modules.isSheaf F⟩ : TopCat.Sheaf Ab X)
    O (f ⁻¹ᵁ V) (fun a => homOfLE (hOV a)) hcov sO hcompat
  refine ⟨((Scheme.Modules.pushforward f).obj F).presheaf.germ V y hyV t, fun a => ?_⟩
  rw [fibreStalkComparison_germ]
  have hxO : x a ∈ O (some a) := ⟨show f (x a) ∈ V from (hxy a) ▸ hyV, hxU a⟩
  rw [← F.presheaf.germ_res_apply (homOfLE (hOV (some a))) (x a) hxO t, ht (some a)]
  show F.presheaf.germ (O (some a)) (x a) hxO
    (F.presheaf.map (homOfLE inf_le_right).op (s a)) = m a
  rw [F.presheaf.germ_res_apply, hs]

/-- Distinct generic points of irreducible components of the support of `F`, a locally finite
family, are separated by opens meeting the support only in their own component. -/
theorem exists_disjoint_opens_of_isGenericPoint_components (F : X.Modules)
    (hclosed : IsClosed (SheafOfModules.supp F))
    (hloc : LocallyFinite (fun Z : irreducibleComponents (SheafOfModules.supp F : Set X) =>
      (Subtype.val '' Z.1 : Set X)))
    {ι : Type u} (x : ι → X) (hinj : Function.Injective x)
    (hgen : ∀ a, ∃ Z : irreducibleComponents (SheafOfModules.supp F : Set X),
      IsGenericPoint (x a) (Subtype.val '' Z.1 : Set X)) :
    ∃ E : ι → X.Opens, (∀ a, x a ∈ E a) ∧
      ∀ a b, a ≠ b → ∀ z, z ∈ E a → z ∈ E b → z ∉ SheafOfModules.supp F := by
  classical
  let T := SheafOfModules.supp F
  let Comp := irreducibleComponents (T : Set X)
  let Z : Comp → Set X := fun I => Subtype.val '' I.1
  have hc (I : Comp) : IsClosed (Z I) :=
    hclosed.isClosedEmbedding_subtypeVal.isClosedMap _
      (isClosed_of_mem_irreducibleComponents I.1 I.2)
  choose I hI using hgen
  have huniq (a : ι) (J : Comp) (ha : x a ∈ Z J) : I a = J := by
    have hsub : Z (I a) ⊆ Z J := by
      show Subtype.val '' (I a).1 ⊆ Z J
      rw [← (hI a).def]
      exact closure_minimal (Set.singleton_subset_iff.mpr ha) (hc J)
    refine Subtype.ext (le_antisymm (fun z hz => ?_) ?_)
    · obtain ⟨w, hw, he⟩ := hsub ⟨z, hz, rfl⟩
      simpa [show w = z from Subtype.ext he] using hw
    · refine (I a).2.2 J.2.1 fun z hz => ?_
      obtain ⟨w, hw, he⟩ := hsub ⟨z, hz, rfl⟩
      simpa [show w = z from Subtype.ext he] using hw
  let E (a : ι) : X.Opens := ⟨(⋃ J : {J : Comp // J ≠ I a}, Z J.1)ᶜ,
    ((hloc.comp_injective Subtype.val_injective).isClosed_iUnion fun J => hc J.1).isOpen_compl⟩
  refine ⟨E, fun a ha => ?_, fun a b hab z hza hzb hz => ?_⟩
  · obtain ⟨J, hJ⟩ := Set.mem_iUnion.mp ha
    exact J.2 (huniq a J.1 hJ).symm
  · let J : Comp := ⟨irreducibleComponent (⟨z, hz⟩ : T),
      irreducibleComponent_mem_irreducibleComponents _⟩
    have hzJ : z ∈ Z J := ⟨⟨z, hz⟩, mem_irreducibleComponent, rfl⟩
    have hJa : J = I a := of_not_not fun h => hza (Set.mem_iUnion.mpr ⟨⟨J, h⟩, hzJ⟩)
    have hJb : J = I b := of_not_not fun h => hzb (Set.mem_iUnion.mpr ⟨⟨J, h⟩, hzJ⟩)
    exact hab (hinj ((hI a).eq (by simpa [← hJa, hJb] using hI b)))

/-- The module structure on the stalk of `F` at a point of the support fibre, by restriction of
scalars along the stalk map of `f`. -/
@[instance_reducible]
def supportFibreStalkModule (f : X ⟶ Y) (F : X.Modules) (y : Y)
    (x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F}) :
    Module (Y.presheaf.stalk y) (F.presheaf.stalk x.1) := by
  rcases x with ⟨x, hxy, hxF⟩
  subst hxy
  exact Module.compHom _ (f.stalkMap x).hom

/-- The comparison from the stalk of `f_* F` at `y` to the stalk of `F` at a point of the
support fibre. -/
def supportFibreStalkLinearMap (f : X ⟶ Y) (F : X.Modules) (y : Y)
    (x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F}) :
    letI := supportFibreStalkModule f F y x
    ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y →ₗ[Y.presheaf.stalk y]
      F.presheaf.stalk x.1 := by
  rcases x with ⟨x, hxy, hxF⟩
  subst hxy
  exact stalkLinearMapOverBase f F x

/-- The comparison `supportFibreStalkLinearMap` applied to a germ of `f_* F` at `y` is
`fibreStalkComparison` of that germ. -/
theorem supportFibreStalkLinearMap_apply (f : X ⟶ Y) (F : X.Modules) (y : Y)
    (x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F})
    (t : ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y) :
    letI := supportFibreStalkModule f F y x
    supportFibreStalkLinearMap f F y x t = fibreStalkComparison f F y x.1 x.2.1 t := by
  rcases x with ⟨x, hxy, hxF⟩
  subst hxy
  rfl

/-- **The stalk of a direct image along the fibre of the support.** For a closed morphism
`f : X ⟶ Y` and an `𝒪_X`-module `F` with closed support and locally finite family of support
components, if every point of the support over `y` is the generic point of a component of the
support, then the stalk of `f_* F` at `y` is the product of the stalks of `F` along that fibre. -/
def pushforwardStalkLinearEquivPi (f : X ⟶ Y) [UniversallyClosed f] (F : X.Modules)
    (hclosed : IsClosed (SheafOfModules.supp F)) (y : Y)
    (hloc : LocallyFinite (fun Z : irreducibleComponents (SheafOfModules.supp F : Set X) =>
      (Subtype.val '' Z.1 : Set X)))
    (hgen : ∀ x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F},
      ∃ Z : irreducibleComponents (SheafOfModules.supp F : Set X),
        IsGenericPoint x.1 (Subtype.val '' Z.1 : Set X)) :
    letI : ∀ x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F},
        Module (Y.presheaf.stalk y) (F.presheaf.stalk x.1) :=
      supportFibreStalkModule f F y
    ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y ≃ₗ[Y.presheaf.stalk y]
      (∀ x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F}, F.presheaf.stalk x.1) := by
  letI : ∀ x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F},
      Module (Y.presheaf.stalk y) (F.presheaf.stalk x.1) :=
    supportFibreStalkModule f F y
  refine LinearEquiv.ofBijective (LinearMap.pi (supportFibreStalkLinearMap f F y)) ⟨?_, ?_⟩
  · intro s t hst
    refine sub_eq_zero.mp
      (eq_zero_of_forall_fibreStalkComparison_eq_zero f F hclosed y (s - t) fun z hzy hzF => ?_)
    have he := congrFun hst ⟨z, hzy, hzF⟩
    change supportFibreStalkLinearMap f F y ⟨z, hzy, hzF⟩ s =
      supportFibreStalkLinearMap f F y ⟨z, hzy, hzF⟩ t at he
    rw [supportFibreStalkLinearMap_apply, supportFibreStalkLinearMap_apply] at he
    rw [fibreStalkComparison_sub f F y z hzy s t, he, sub_self]
  · intro m
    obtain ⟨E, hE, hdis⟩ := exists_disjoint_opens_of_isGenericPoint_components F hclosed hloc
      (fun x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F} => x.1) Subtype.val_injective hgen
    obtain ⟨t, ht⟩ := exists_fibreStalkComparison_eq f F hclosed y
      (fun x : ↥{x : X | f x = y ∧ x ∈ SheafOfModules.supp F} => x.1) (fun x => x.2.1)
      (fun z hz hzy => ⟨⟨z, hzy, hz⟩, rfl⟩) E hE hdis m
    exact ⟨t, funext fun a => (supportFibreStalkLinearMap_apply f F y a t).trans (ht a)⟩

/-! ### Lengths of stalks over the base -/

/-- The length of the stalk of `F` at `x` over the local ring of `Y` at `f x` is its length over
the local ring of `X` at `x` times the residue degree of `f` at `x`. -/
theorem length_stalk_restrictScalars_toNat (f : X ⟶ Y) (F : X.Modules) (x : X) :
    letI : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
      Module.compHom _ (f.stalkMap x).hom
    (Module.length (Y.presheaf.stalk (f x)) (F.presheaf.stalk x)).toNat =
      (Module.length (X.presheaf.stalk x) (F.presheaf.stalk x)).toNat * f.residueDegree x := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    ⟨fun a b m => mul_smul ((f.stalkMap x).hom a) b m⟩
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    (inferInstance : IsLocalHom (f.stalkMap x).hom)
  rw [IsLocalRing.length_restrictScalars (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    (F.presheaf.stalk x), ENat.toNat_mul, Module.length_eq_rank, Cardinal.toNat_toENat]
  congr 1
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (inferInstance : Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)))
  have hA : (inferInstance : Algebra (Y.residueField (f x)) (X.residueField x)) =
      (f.residueFieldMap x).hom.toAlgebra := by
    refine Algebra.algebra_ext _ _ fun a => ?_
    obtain ⟨b, rfl⟩ := Y.residue_surjective (f x) a
    rfl
  show @Module.finrank (Y.residueField (f x)) (X.residueField x) _ _
    (inferInstance : Algebra (Y.residueField (f x)) (X.residueField x)).toModule = _
  rw [hA]
  rfl

end Stacks.Chow

end
